/*
 * Copyright (c) 2020, Jack Lange <jacklange@cs.pitt.edu>
 * All rights reserved.
 *
 * This is free software.  You are permitted to use,
 * redistribute, and modify it as specified in the file "PETLAB_LICENSE".
 */

#include <string.h>
#include <errno.h>

#include <petnet.h>

#include <petlib/pet_util.h>
#include <petlib/pet_log.h>
#include <petlib/pet_hashtable.h>
#include <petlib/pet_json.h>

#include <util/ip_address.h>
#include <util/inet.h>
#include <util/checksum.h>

#include "ethernet.h"
#include "ipv4.h"
#include "tcp.h"
#include "tcp_connection.h"
#include "packet.h"
#include "socket.h"
#include "timer.h"

#define TIMEOUT_TIME_SEC 1

extern int petnet_errno;

struct tcp_state {
	struct tcp_con_map * con_map;
};


static inline struct tcp_raw_hdr *
__get_tcp_hdr(struct packet * pkt)
{
	struct tcp_raw_hdr * tcp_hdr = pkt->layer_2_hdr + pkt->layer_2_hdr_len + pkt->layer_3_hdr_len;

	pkt->layer_4_type	 = TCP_PKT;
	pkt->layer_4_hdr	 = tcp_hdr;
	pkt->layer_4_hdr_len = tcp_hdr->header_len * 4;

	return tcp_hdr;
}


static inline struct tcp_raw_hdr *
__make_tcp_hdr(struct packet * pkt,
			   uint32_t		   option_len)
{
	pkt->layer_4_type	 = TCP_PKT;
	pkt->layer_4_hdr	 = pet_malloc(sizeof(struct tcp_raw_hdr) + option_len);
	pkt->layer_4_hdr_len = sizeof(struct tcp_raw_hdr) + option_len;

	return (struct tcp_raw_hdr *)(pkt->layer_4_hdr);
}

static inline void *
__get_payload(struct packet * pkt)
{
	if (pkt->layer_3_type == IPV4_PKT) {
		struct ipv4_raw_hdr * ipv4_hdr = pkt->layer_3_hdr;

		pkt->payload	 = pkt->layer_4_hdr + pkt->layer_4_hdr_len;
		pkt->payload_len = ntohs(ipv4_hdr->total_len) - (pkt->layer_3_hdr_len + pkt->layer_4_hdr_len);

		return pkt->payload;
	} else {
		log_error("Unhandled layer 3 packet format\n");
		return NULL;
	}
}

/// 4.) copy over __calculate_chksum and tcp_send
// copied from udp.c
// changes:
// struct tcp_connection * con
// IPV4_PROTO_TCP
static uint16_t
__calculate_chksum(struct tcp_connection * con,
				   struct ipv4_addr *	   remote_addr,
				   struct packet *		   pkt)
{
	struct ipv4_pseudo_hdr hdr;
	uint16_t			   checksum = 0;	// checksum starts at 0 so that we can start adding the words

	memset(&hdr, 0, sizeof(struct ipv4_pseudo_hdr));

	ipv4_addr_to_octets(con->ipv4_tuple.local_ip, hdr.src_ip);
	ipv4_addr_to_octets(remote_addr, hdr.dst_ip);

	hdr.proto  = IPV4_PROTO_TCP;
	hdr.length = htons(pkt->layer_4_hdr_len + pkt->payload_len);

	checksum = calculate_checksum_begin(&hdr, sizeof(struct ipv4_pseudo_hdr) / 2);
	checksum = calculate_checksum_continue(checksum, pkt->layer_4_hdr, pkt->layer_4_hdr_len / 2);
	checksum = calculate_checksum_continue(checksum, pkt->payload, pkt->payload_len / 2);


	/*
	 * If there is an odd number of data bytes we have to include a 0-byte after the the last byte
	 */
	if ((pkt->payload_len % 2) != 0) {
		uint16_t tmp = *(uint8_t *)(pkt->payload + pkt->payload_len - 1);

		checksum = calculate_checksum_finalize(checksum, &tmp, 1);
	} else {
		checksum = calculate_checksum_finalize(checksum, NULL, 0);
	}

	return checksum;
}

static void __retransmit_timeout(struct pet_timeout * timeout, void * arg)
{
	pet_printf("retransmit timeout fired!\n");
	struct tcp_connection * con = (struct tcp_connection *)arg;
	lock_tcp_con(con);
	con->timed_out = 1;
	unlock_tcp_con(con);
}


/// 5.) write helper function
static int
__send_syn_ack(struct tcp_connection * con,
			   struct ipv4_addr *	   remote_addr,
			   uint16_t				   remote_port)
{
	struct packet *		 pkt	  = NULL;
	struct tcp_raw_hdr * tcp_hdr  = NULL;
	uint16_t			 checksum = 0;

	// create empty packet
	pkt		= create_empty_packet();
	tcp_hdr = __make_tcp_hdr(pkt, 0);

	// fill in TCP header fields
	// more info in section 3.7 https://datatracker.ietf.org/doc/html/rfc793
	tcp_hdr->src_port = htons(con->ipv4_tuple.local_port);	  // our port
	tcp_hdr->dst_port = htons(remote_port);					  // remote port
	tcp_hdr->seq_num  = htonl(con->snd_nxt);				  // sender keeps track of next seq num to use
	tcp_hdr->ack_num  = htonl(con->rcv_nxt);				  // ack_num tells remote side what byte we expect next
															  // rcv_nxt = their seq_num + 1 (syn consumes one sequence number)

	// header_len stores number of 32 bit (4 byte) words
	// sizeof(struct tcp_raw_hdr) will be in bytes
	// divide by 4 to get however many # of 4-byte words we have
	tcp_hdr->header_len = sizeof(struct tcp_raw_hdr) / 4;	 // convert from bytes to words by dividing by 4
	tcp_hdr->flags.SYN	= 1;
	tcp_hdr->flags.ACK	= 1;
	// use max receive for now ***
	tcp_hdr->recv_win = htons(65535);	 // = 2^16 - 1 = max value of uint16_t = max receive
	tcp_hdr->checksum = 0;				 // checksum field must be 0 before calculating

	// syn ack doesn't have payload
	pkt->payload	 = NULL;
	pkt->payload_len = 0;

	checksum		  = __calculate_chksum(con, remote_addr, pkt);
	tcp_hdr->checksum = checksum;

	// give packet to ipv4 layer for transmission
	// ipv4 layer handles everything below tcp
	if (ipv4_pkt_tx(pkt, remote_addr) != 0) {
		log_error("Failed to send SYN ACK\n");
		goto err;
	}

	return 0;

err:
	// we need to free packet if ipv4_pkt_tx fails
	// otherwise it's freed on success
	if (pkt)
		free_packet(pkt);
	return -1;
}

/// 7.) helper function to ack incoming packets
static int
__send_ack(struct tcp_connection * con,
		   struct ipv4_addr *	   remote_addr,
		   uint16_t				   remote_port)
{
	struct packet *		 pkt	  = NULL;
	struct tcp_raw_hdr * tcp_hdr  = NULL;
	uint16_t			 checksum = 0;

	// create empty packet
	pkt		= create_empty_packet();
	tcp_hdr = __make_tcp_hdr(pkt, 0);

	// fill in TCP header fields
	// more info in section 3.7 https://datatracker.ietf.org/doc/html/rfc793
	tcp_hdr->src_port = htons(con->ipv4_tuple.local_port);	  // our port
	tcp_hdr->dst_port = htons(remote_port);					  // remote port
	tcp_hdr->seq_num  = htonl(con->snd_nxt);				  // sender keeps track of next seq num to use
	tcp_hdr->ack_num  = htonl(con->rcv_nxt);				  // rcv_nxt updated by payload_len

	// header_len stores number of 32 bit (4 byte) words
	// sizeof(struct tcp_raw_hdr) will be in bytes
	// divide by 4 to get however many # of 4-byte words we have
	tcp_hdr->header_len = sizeof(struct tcp_raw_hdr) / 4;	 // convert from bytes to words by dividing by 4
	tcp_hdr->flags.ACK	= 1;
	// use max receive for now ***
	tcp_hdr->recv_win = htons(65535);	 // = 2^16 - 1 = max value of uint16_t = max receive
	tcp_hdr->checksum = 0;				 // checksum field must be 0 before calculating

	// ack doesn't have payload
	pkt->payload	 = NULL;
	pkt->payload_len = 0;

	checksum		  = __calculate_chksum(con, remote_addr, pkt);
	tcp_hdr->checksum = checksum;

	// give packet to ipv4 layer for transmission
	// ipv4 layer handles everything below tcp
	if (ipv4_pkt_tx(pkt, remote_addr) != 0) {
		log_error("Failed to send ACK\n");
		goto err;
	}

	return 0;

err:
	// we need to free packet if ipv4_pkt_tx fails
	// otherwise it's freed on success
	if (pkt)
		free_packet(pkt);
	return -1;
}

/// 8.) helper function to send ack+fin (combined step)
// once we (the server) receive a fin, we can send an ack and a fin together
// and move from ESTABLISHED to CLOSE_WAIT to LAST_ACK
static int
__send_fin_ack(struct tcp_connection * con,
			   struct ipv4_addr *	   remote_addr,
			   uint16_t				   remote_port)
{
	struct packet *		 pkt	  = NULL;
	struct tcp_raw_hdr * tcp_hdr  = NULL;
	uint16_t			 checksum = 0;

	// create empty packet
	pkt		= create_empty_packet();
	tcp_hdr = __make_tcp_hdr(pkt, 0);

	// fill in TCP header fields
	// more info in section 3.7 https://datatracker.ietf.org/doc/html/rfc793
	tcp_hdr->src_port = htons(con->ipv4_tuple.local_port);	  // our port
	tcp_hdr->dst_port = htons(remote_port);					  // remote port
	tcp_hdr->seq_num  = htonl(con->snd_nxt);				  // sender keeps track of next seq num to use
	tcp_hdr->ack_num  = htonl(con->rcv_nxt);				  // rcv_nxt

	// header_len stores number of 32 bit (4 byte) words
	// sizeof(struct tcp_raw_hdr) will be in bytes
	// divide by 4 to get however many # of 4-byte words we have
	tcp_hdr->header_len = sizeof(struct tcp_raw_hdr) / 4;	 // convert from bytes to words by dividing by 4
	tcp_hdr->flags.ACK	= 1;
	tcp_hdr->flags.FIN	= 1;
	// use max receive for now ***
	tcp_hdr->recv_win = htons(65535);	 // = 2^16 - 1 = max value of uint16_t = max receive
	tcp_hdr->checksum = 0;				 // checksum field must be 0 before calculating

	// ack doesn't have payload
	pkt->payload	 = NULL;
	pkt->payload_len = 0;

	checksum		  = __calculate_chksum(con, remote_addr, pkt);
	tcp_hdr->checksum = checksum;

	// give packet to ipv4 layer for transmission
	// ipv4 layer handles everything below tcp
	if (ipv4_pkt_tx(pkt, remote_addr) != 0) {
		log_error("Failed to send ACK+FIN\n");
		goto err;
	}

	return 0;

err:
	// we need to free packet if ipv4_pkt_tx fails
	// otherwise it's freed on success
	if (pkt)
		free_packet(pkt);
	return -1;
}


/// 8.) helper function to send data packet
// modified other send funcs
static int
__send_data_pkt(struct tcp_connection * con)
{
	struct packet *		 pkt	  = NULL;
	struct tcp_raw_hdr * tcp_hdr  = NULL;
	uint16_t			 checksum = 0;
	uint32_t			 data_len = 0;

	// checks how much data is waiting in sockets send buffer
	data_len = pet_socket_send_capacity(con->sock);

	pet_printf("DEBUG1: __send_data_pkt: data_len=%u snd_nxt=%u snd_una=%u timed_out=%d\n", data_len, con->snd_nxt, con->snd_una, con->timed_out);

	if (data_len == 0) {
		pet_printf("DEBUG2: __send_data_pkt: nothing to send\n");
		return 0;
	}

	// create empty packet
	pkt		= create_empty_packet();
	tcp_hdr = __make_tcp_hdr(pkt, 0);

	// fill in TCP header fields
	// more info in section 3.7 https://datatracker.ietf.org/doc/html/rfc793
	tcp_hdr->src_port = htons(con->local_port);		// our port
	tcp_hdr->dst_port = htons(con->remote_port);	// remote port
	tcp_hdr->seq_num  = htonl(con->snd_nxt);		// sender keeps track of next seq num to use
	tcp_hdr->ack_num  = htonl(con->rcv_nxt);		// rcv_nxt

	// header_len stores number of 32 bit (4 byte) words
	// sizeof(struct tcp_raw_hdr) will be in bytes
	// divide by 4 to get however many # of 4-byte words we have
	tcp_hdr->header_len = sizeof(struct tcp_raw_hdr) / 4;	 // convert from bytes to words by dividing by 4
	tcp_hdr->flags.ACK	= 1;

	// use max receive for now ***
	tcp_hdr->recv_win = htons(65535);	 // = 2^16 - 1 = max value of uint16_t = max receive
	tcp_hdr->checksum = 0;				 // checksum field must be 0 before calculating

	// ack doesn't have payload
	pkt->payload	 = pet_malloc(data_len);
	pkt->payload_len = data_len;

	// pulls data out of sockets send buff and copies it into packets payload
	pet_socket_sending_data(con->sock, pkt->payload, data_len);

	con->snd_una = con->snd_nxt;

	// advances seq # by how many bytes we sent
	con->snd_nxt = con->snd_nxt + data_len;

	checksum = __calculate_chksum(con, con->remote_ip, pkt);

	tcp_hdr->checksum = checksum;

	// give packet to ipv4 layer for transmission
	// ipv4 layer handles everything below tcp
	if (ipv4_pkt_tx(pkt, con->remote_ip) != 0) {
		log_error("Failed to send data packet\n");
		goto err;
	}

	con->timed_out = 0;
	con->timeout   = pet_add_timeout(TIMEOUT_TIME_SEC, __retransmit_timeout, con);
	pet_printf("DEBUG3: __send_data_pkt: sent %u bytes, timer started\n", data_len);

	return 0;

err:
	// we need to free packet if ipv4_pkt_tx fails
	// otherwise it's freed on success
	if (pkt)
		free_packet(pkt);
	return -1;
}

// helper function. same as send_syn_ack but without the ack
static int
__send_syn(struct tcp_connection * con,
		   struct ipv4_addr *	   remote_addr,
		   uint16_t				   remote_port)
{
	struct packet *		 pkt	  = NULL;
	struct tcp_raw_hdr * tcp_hdr  = NULL;
	uint16_t			 checksum = 0;

	// create empty packet
	pkt		= create_empty_packet();
	tcp_hdr = __make_tcp_hdr(pkt, 0);

	// fill in TCP header fields
	// more info in section 3.7 https://datatracker.ietf.org/doc/html/rfc793
	tcp_hdr->src_port = htons(con->ipv4_tuple.local_port);	  // our port
	tcp_hdr->dst_port = htons(remote_port);					  // remote port
	tcp_hdr->seq_num  = htonl(con->snd_nxt);				  // sender keeps track of next seq num to use
	tcp_hdr->ack_num  = 0;									  // not used in SYN, set to 0

	// header_len stores number of 32 bit (4 byte) words
	// sizeof(struct tcp_raw_hdr) will be in bytes
	// divide by 4 to get however many # of 4-byte words we have
	tcp_hdr->header_len = sizeof(struct tcp_raw_hdr) / 4;	 // convert from bytes to words by dividing by 4
	tcp_hdr->flags.SYN	= 1;
	// use max receive for now ***
	tcp_hdr->recv_win = htons(65535);	 // = 2^16 - 1 = max value of uint16_t = max receive
	tcp_hdr->checksum = 0;				 // checksum field must be 0 before calculating

	// syn ack doesn't have payload
	pkt->payload	 = NULL;
	pkt->payload_len = 0;

	checksum		  = __calculate_chksum(con, remote_addr, pkt);
	tcp_hdr->checksum = checksum;

	// give packet to ipv4 layer for transmission
	// ipv4 layer handles everything below tcp
	if (ipv4_pkt_tx(pkt, remote_addr) != 0) {
		log_error("Failed to send SYN ACK\n");
		goto err;
	}

	return 0;

err:
	// we need to free packet if ipv4_pkt_tx fails
	// otherwise it's freed on success
	if (pkt)
		free_packet(pkt);
	return -1;
}


pet_json_obj_t
tcp_hdr_to_json(struct tcp_raw_hdr * hdr)
{
	pet_json_obj_t hdr_json = PET_JSON_INVALID_OBJ;

	hdr_json = pet_json_new_obj("TCP Header");

	if (hdr_json == PET_JSON_INVALID_OBJ) {
		log_error("Could not create TCP Header JSON\n");
		goto err;
	}

	pet_json_add_u16(hdr_json, "src port", ntohs(hdr->src_port));
	pet_json_add_u16(hdr_json, "dst port", ntohs(hdr->dst_port));
	pet_json_add_u32(hdr_json, "seq num", ntohl(hdr->seq_num));
	pet_json_add_u32(hdr_json, "ack num", ntohl(hdr->ack_num));
	pet_json_add_u8(hdr_json, "header len", hdr->header_len * 4);
	pet_json_add_bool(hdr_json, "URG flag", hdr->flags.URG);
	pet_json_add_bool(hdr_json, "ACK flag", hdr->flags.ACK);
	pet_json_add_bool(hdr_json, "PSH flag", hdr->flags.PSH);
	pet_json_add_bool(hdr_json, "RST flag", hdr->flags.RST);
	pet_json_add_bool(hdr_json, "SYN flag", hdr->flags.SYN);
	pet_json_add_bool(hdr_json, "FIN flag", hdr->flags.FIN);
	pet_json_add_u16(hdr_json, "recv win", ntohs(hdr->recv_win));
	pet_json_add_u16(hdr_json, "checksum", ntohs(hdr->checksum));
	pet_json_add_u16(hdr_json, "urgent ptr", ntohs(hdr->urgent_ptr));


	return hdr_json;

err:
	if (hdr_json != PET_JSON_INVALID_OBJ)
		pet_json_free(hdr_json);

	return PET_JSON_INVALID_OBJ;
}


void print_tcp_header(struct tcp_raw_hdr * tcp_hdr)
{
	pet_json_obj_t hdr_json = PET_JSON_INVALID_OBJ;

	char * json_str = NULL;

	hdr_json = tcp_hdr_to_json(tcp_hdr);

	if (hdr_json == PET_JSON_INVALID_OBJ) {
		log_error("Could not serialize TCP Header to JSON\n");
		return;
	}

	json_str = pet_json_serialize(hdr_json);

	pet_printf("\"TCP Header\": %s\n", json_str);

	pet_free(json_str);
	pet_json_free(hdr_json);

	return;
}


int tcp_listen(struct socket *	  sock,
			   struct ipv4_addr * local_addr,
			   uint16_t			  local_port)
{
	// get TCP module's global state (w/ connection map)
	// hashtable: IP tuples to tcp_connection objects
	struct tcp_state * tcp_state = petnet_state->tcp_state;

	/// 2.) implement tcp_listen in tcp.c
	// copied code from udp.c (udp_bind)
	struct tcp_connection * con = NULL;
	// remote_ip is 0.0.0.0 because we don't know who will connect yet
	struct ipv4_addr * remote_ip = ipv4_addr_from_str("0.0.0.0");

	/// 1.) add print statements to all 5 method stubs in tcp.c:
	// tcp_listen, tcp_connect_ipv4, tcp_send, tcp_close, tcp_pkt_rx
	pet_printf("tcp_listen entered\n");

	// create new connection object
	// set parameters remote_ip and remote_port to NULL and
	// ipv4_addr_from_str("0.0.0.0")
	// because we are just listening right now,
	// we don't know who will connect
	con = create_ipv4_tcp_con(tcp_state->con_map, local_addr, remote_ip, local_port, 0);

	// free immediately, create_ipv4_tcp_con in tcp_connection.c creates internal copy
	free_ipv4_addr(remote_ip);
	remote_ip = NULL;

	// if err, create_ipv4_tcp_con returns null
	if (con == NULL) {
		pet_socket_error(sock, EINVAL);
		goto err;
	}

	// associate the socket with this connection so
	// that we can look up this connection later
	// using the socket pointer (tcp_send, tcp_close)
	add_sock_to_tcp_con(tcp_state->con_map, con, sock);

	// move to LISTEN state
	// ready to receive incoming SYNs
	con->con_state = LISTEN;
	// set initial sequence number
	con->snd_nxt   = 4242;	  // choosing something arbitrary for now
	con->timed_out = 0;
	con->timeout   = NULL;

	// unlock and release the reference before returning
	put_and_unlock_tcp_con(con);

	return 0;

err:

	if (con)
		put_and_unlock_tcp_con(con);

	return -1;
}

// what is called when app calls petnet_connect()
// lowk same as tcp_listen but we move to SYN_SENT state instead of LISTEN and we send a SYN instead of just waiting for one
int tcp_connect_ipv4(struct socket *	sock,
					 struct ipv4_addr * local_addr,
					 uint16_t			local_port,
					 struct ipv4_addr * remote_addr,
					 uint16_t			remote_port)
{
	// get TCP module's global state (w/ connection map)
	// hashtable: IP tuples to tcp_connection objects
	struct tcp_state * tcp_state = petnet_state->tcp_state;

	/// 2.) implement tcp_listen in tcp.c
	// copied code from udp.c (udp_bind)
	struct tcp_connection * con = NULL;
	// remote_ip is 0.0.0.0 because we don't know who will connect yet
	struct ipv4_addr * remote_ip = ipv4_addr_from_str("0.0.0.0");

	/// 1.) add print statements to all 5 method stubs in tcp.c:
	// tcp_listen, tcp_connect_ipv4, tcp_send, tcp_close, tcp_pkt_rx
	pet_printf("tcp_connect_ipv4 entered\n");

	// create new connection object
	// set parameters remote_ip and remote_port to NULL and
	// ipv4_addr_from_str("0.0.0.0")
	// because we are just listening right now,
	// we don't know who will connect
	con = create_ipv4_tcp_con(tcp_state->con_map, local_addr, remote_ip, local_port, 0);

	// free immediately, create_ipv4_tcp_con in tcp_connection.c creates internal copy
	free_ipv4_addr(remote_ip);
	remote_ip = NULL;

	// if err, create_ipv4_tcp_con returns null
	if (con == NULL) {
		pet_socket_error(sock, EINVAL);
		goto err;
	}

	// associate the socket with this connection so
	// that we can look up this connection later
	// using the socket pointer (tcp_send, tcp_close)
	add_sock_to_tcp_con(tcp_state->con_map, con, sock);

	con->con_state	 = SYN_SENT;	// we sent a SYN, waiting for SYN-ACK
	con->snd_nxt	 = 4242;
	con->remote_ip	 = ipv4_addr_clone(remote_addr);
	con->remote_port = remote_port;
	con->local_port	 = local_port;
	con->timed_out	 = 0;
	con->timeout	 = NULL;

	__send_syn(con, remote_addr, remote_port);	  // send SYN to kick off the handshake


	// unlock and release the reference before returning
	put_and_unlock_tcp_con(con);

	return 0;

err:

	if (con)
		put_and_unlock_tcp_con(con);

	return -1;
}


// unused for now
// entire function provided + copied from project 2 pdf
int tcp_send(struct socket * sock)
{
	struct tcp_state *		tcp_state = petnet_state->tcp_state;
	struct tcp_connection * con		  = get_and_lock_tcp_con_from_sock(tcp_state->con_map, sock);

	pet_printf("tcp_send\n");	 //
	if (con == NULL) {
		log_error("could not find TCP connection (called from tcp_send)\n");
		return -1;
	}

	if (con->timed_out) {
		pet_printf("retransmitting due to TIMEOUT!!\n");
		con->snd_nxt   = con->snd_una;
		con->timed_out = 0;
	}

	if (con->con_state != ESTABLISHED) {
		log_error("TCP Connection is not established\n");
		goto err;
	}
	__send_data_pkt(con);
	put_and_unlock_tcp_con(con);
	return 0;

err:
	if (con)
		put_and_unlock_tcp_con(con);
	return -1;
}


/* Petnet assumes SO_LINGER semantics, so if we'ere here there is no pending write data */
int tcp_close(struct socket * sock)
{
	struct tcp_state *		tcp_state = petnet_state->tcp_state;
	struct tcp_connection * con		  = get_and_lock_tcp_con_from_sock(tcp_state->con_map, sock);

	pet_printf("tcp_close\n");

	if (con == NULL) {
		log_error("could not find TCP connection (called from tcp_close)\n");
		return -1;
	}

	if (con->con_state == ESTABLISHED) {
		__send_fin_ack(con, con->remote_ip, con->remote_port);
		con->snd_nxt   = con->snd_nxt + 1;	  // fin uses 1 seq number
		con->con_state = FIN_WAIT1;			  // i think i must check
		pet_printf("sent FIN, moved to FIN_WAIT1\n");
	}

	put_and_unlock_tcp_con(con);
	return 0;
}


int tcp_pkt_rx(struct packet * pkt)
{
	if (pkt->layer_3_type == IPV4_PKT) {
		// Handle IPV4 Packet

		/*
		/// 3.) start writing tcp_pkt_rx
		struct tcp_raw_hdr * tcp_hdr = NULL;

		// parse TCP header
		// fills in pkt->layer_4_hdr, layer_4_hdr_len
		tcp_hdr = __get_tcp_hdr(pkt);

		// just print header for now
		pet_printf("received TCP segment\n");
		print_tcp_header(tcp_hdr);
		*/

		/// 6.) fill out more of tcp_pkt_rx
		struct tcp_state *		tcp_state = petnet_state->tcp_state;
		struct tcp_raw_hdr *	tcp_hdr	  = NULL;
		struct ipv4_raw_hdr *	ipv4_hdr  = (struct ipv4_raw_hdr *)pkt->layer_3_hdr;
		struct ipv4_addr *		src_ip	  = NULL;
		struct ipv4_addr *		dst_ip	  = NULL;
		struct ipv4_addr *		zero_ip	  = NULL;
		struct tcp_connection * con		  = NULL;
		uint16_t				src_port  = 0;
		uint16_t				dst_port  = 0;

		// tcp_pkt_rx is the entry point for all incoming TCP segments
		// current implementation handles:
		// guide step 3) parse and print incoming segments
		// guide step 6) extract ips/ports, look up connection, handle syn
		// step 6)
		// parse tcp and ipv4 headers to extract src/dst ips and ports
		// look up LISTEN connection in map using dst_ip and dst_port
		// we initially stored this with 0.0.0.0 for remote_ip in tcp_listen()
		// if we are in LISTEN and we see syn flag,
		// record remote's seq_num + 1 into rcv_nxt (next byte we expect)
		// b/c syn consumes 1 seq num
		// send syn ack
		// transition to state SYN_RCVD
		// next steps:
		// handle ack in SYN_RCVD state, move to ESTABLISHED state
		// handle data in ESTABLISHED state
		// handle FIN and close connection

		// parse TCP header from raw packet buffer
		// fills in pkt->layer_4_hdr, layer_4_hdr_len
		tcp_hdr = __get_tcp_hdr(pkt);
		__get_payload(pkt);

		// copied from udp.c
		src_ip = ipv4_addr_from_octets(ipv4_hdr->src_ip);
		dst_ip = ipv4_addr_from_octets(ipv4_hdr->dst_ip);

		// extract ports from TCP header
		src_port = ntohs(tcp_hdr->src_port);
		dst_port = ntohs(tcp_hdr->dst_port);

		// just print header for now
		pet_printf("received TCP segment\n");
		print_tcp_header(tcp_hdr);

		// look up connection by dst_ip and dst_port
		// use 0.0.0.0 for remote because that's what we
		// initially stored in tcp_listen() for LISTEN,
		// since we didn't know remote side at listen time
		// First try exact match (for established connections)
		con = get_and_lock_tcp_con_from_ipv4(tcp_state->con_map,
											 dst_ip,
											 src_ip,
											 dst_port,
											 src_port);

		// If not found, fall back to wildcard listener lookup (for new SYNs)
		if (con == NULL) {
			zero_ip = ipv4_addr_from_str("0.0.0.0");
			con		= get_and_lock_tcp_con_from_ipv4(tcp_state->con_map,
													 dst_ip,
													 zero_ip,
													 dst_port,
													 0);
			free_ipv4_addr(zero_ip);
			zero_ip = NULL;
		}


		// copied from udp.c
		if (con == NULL) {	  // print statement modified to suit TCP
			log_error("Could not find TCP connection\n");
			goto out;
		}

		// state diagram: syn received while in listen state
		// we are in passive open (3-way handshake)
		if (con->con_state == LISTEN && tcp_hdr->flags.SYN) {
			// store remote's next expected byte
			// syn consumes 1 seq number, so expect
			// seq_num + 1 for the next
			// put in ack_num
			con->rcv_nxt = ntohl(tcp_hdr->seq_num) + 1;

			// send syn ack !! yay
			pet_printf("send syn-ack\n");
			__send_syn_ack(con, src_ip, src_port);

			con->snd_nxt = con->snd_nxt + 1;

			// next state = we wait for ack to complete handshake
			con->con_state = SYN_RCVD;
		}

		// we sent a SYN and are waiting for SYN-ACK
		// we are in active open (3-way handshake)
		if (con->con_state == SYN_SENT && tcp_hdr->flags.SYN && tcp_hdr->flags.ACK) {
			con->rcv_nxt   = ntohl(tcp_hdr->seq_num) + 1;
			con->snd_nxt   = con->snd_nxt + 1;
			con->con_state = ESTABLISHED;

			__send_ack(con, src_ip, src_port);	  // send final ACK to complete handshake

			pet_socket_connected(con->sock);	// tell socket layer connection is ready
			pet_printf("SYN-ACK received, sent ACK, connection ESTABLISHED\n");
		}

		// now we wait for ack (after we just sent syn-ack)
		if (con->con_state == SYN_RCVD && tcp_hdr->flags.ACK) {
			struct socket *			new_sock	 = NULL;
			struct tcp_connection * new_con		 = NULL;
			uint32_t				accepted_snd = con->snd_nxt;

			con->con_state = LISTEN;
			con->snd_nxt   = 4242;
			con->rcv_nxt   = 0;

			new_con = create_ipv4_tcp_con(tcp_state->con_map,
										  dst_ip,
										  src_ip,
										  dst_port,
										  src_port);

			if (new_con == NULL) {
				log_error("Could not create new TCP connection for accepted client\n");
				goto out;
			}

			new_con->con_state	 = ESTABLISHED;
			new_con->snd_nxt	 = accepted_snd;
			new_con->rcv_nxt	 = ntohl(tcp_hdr->ack_num);
			new_con->snd_una	 = new_con->snd_nxt;
			new_con->remote_ip	 = ipv4_addr_clone(src_ip);
			new_con->remote_port = src_port;
			new_con->local_port	 = dst_port;
			new_con->timed_out	 = 0;
			new_con->timeout	 = NULL;

			new_sock = pet_socket_accepted(con->sock, src_ip, src_port);

			if (new_sock != NULL) {
				add_sock_to_tcp_con(tcp_state->con_map, new_con, new_sock);
				new_con->sock = new_sock;
				pet_put_socket(new_sock);
			}

			put_and_unlock_tcp_con(new_con);

			pet_printf("ack received, connection established\n");
		}

		// next we ack incoming packets while in ESTABLISHED state
		// (stop and wait)
		// update rcv_nxt by payload_len which tells the remote side
		// how many bytes we received, attach in the ack_num of tcp_hdr
		// (done in __send_ack)
		if (con->con_state == ESTABLISHED && pkt->payload_len > 0) {
			con->rcv_nxt = con->rcv_nxt + pkt->payload_len;	   // important
			pet_socket_received_data(con->sock, pkt->payload, pkt->payload_len);

			__send_ack(con, src_ip, src_port);
			pet_printf("data received, sent ack\n");
		}

		if (con->con_state == ESTABLISHED && tcp_hdr->flags.FIN) {
			con->rcv_nxt = con->rcv_nxt + 1;
			__send_fin_ack(con, src_ip, src_port);
			con->snd_nxt   = con->snd_nxt + 1;
			con->con_state = LAST_ACK;
			pet_printf("received fin, sent fin+ack\n");
		}

		if (con->con_state == ESTABLISHED &&
			tcp_hdr->flags.ACK &&
			pkt->payload_len == 0 &&
			!tcp_hdr->flags.FIN &&
			!tcp_hdr->flags.SYN) {
			if (con->timeout != NULL && con->timed_out == 0) {
				pet_cancel_timeout(con->timeout);
				con->timeout = NULL;
			}
		}

		if (con->con_state == LAST_ACK && tcp_hdr->flags.ACK) {
			struct socket * saved_sock = con->sock;

			con->con_state = CLOSED;
			con->sock	   = NULL;
			remove_tcp_con(tcp_state->con_map, con);
			put_and_unlock_tcp_con(con);
			con = NULL;

			pet_socket_closed(saved_sock);


			pet_printf("final ack received, state -> CLOSED\n");
			goto out;
		}

		if (con->con_state == FIN_WAIT1 && tcp_hdr->flags.ACK) {
			con->con_state = FIN_WAIT2;
			pet_printf("FIN ACKed, moving to FIN_WAIT2\n");
		}

		if (con->con_state == FIN_WAIT2 && pkt->payload_len > 0) {
			con->rcv_nxt = con->rcv_nxt + pkt->payload_len;
			__send_ack(con, src_ip, src_port);
		}

		if (con->con_state == FIN_WAIT2 && tcp_hdr->flags.FIN) {
			con->rcv_nxt = con->rcv_nxt + 1;
			__send_ack(con, src_ip, src_port);
			con->con_state = CLOSED;
			con->sock	   = NULL;
			remove_tcp_con(tcp_state->con_map, con);
			put_and_unlock_tcp_con(con);
			con = NULL;


			pet_printf("received FIN, sent ACK, connection CLOSED\n");
			goto out;
		}


	out:
		if (con)
			put_and_unlock_tcp_con(con);
		if (src_ip)
			free_ipv4_addr(src_ip);
		if (dst_ip)
			free_ipv4_addr(dst_ip);
	}

	return 0;
}

int tcp_init(struct petnet * petnet_state)
{
	struct tcp_state * state = pet_malloc(sizeof(struct tcp_state));

	state->con_map = create_tcp_con_map();

	petnet_state->tcp_state = state;

	return 0;
}