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


extern int petnet_errno;

struct tcp_state {
    struct tcp_con_map * con_map;
};



static inline struct tcp_raw_hdr *
__get_tcp_hdr(struct packet * pkt)
{
    struct tcp_raw_hdr * tcp_hdr = pkt->layer_2_hdr + pkt->layer_2_hdr_len + pkt->layer_3_hdr_len;

    pkt->layer_4_type    = TCP_PKT;
    pkt->layer_4_hdr     = tcp_hdr;
    pkt->layer_4_hdr_len = tcp_hdr->header_len * 4;

    return tcp_hdr;
}


static inline struct tcp_raw_hdr *
__make_tcp_hdr(struct packet * pkt, 
               uint32_t        option_len)
{
    pkt->layer_4_type    = TCP_PKT;
    pkt->layer_4_hdr     = pet_malloc(sizeof(struct tcp_raw_hdr) + option_len);
    pkt->layer_4_hdr_len = sizeof(struct tcp_raw_hdr) + option_len;

    return (struct tcp_raw_hdr *)(pkt->layer_4_hdr);
}

static inline void *
__get_payload(struct packet * pkt)
{
    if (pkt->layer_3_type == IPV4_PKT) {
        struct ipv4_raw_hdr * ipv4_hdr = pkt->layer_3_hdr;

        pkt->payload     = pkt->layer_4_hdr + pkt->layer_4_hdr_len;
        pkt->payload_len = ntohs(ipv4_hdr->total_len) - (pkt->layer_3_hdr_len + pkt->layer_4_hdr_len);

        return pkt->payload;
    } else {
        log_error("Unhandled layer 3 packet format\n");
        return NULL;
    }

}

// CALCULATE CHECKSUM HELPER FUNC (taken from udp.c and modified)
// i literally dont know what it does and i simply do not care. it calculate checksum :)
static uint16_t 
__calculate_chksum(struct tcp_connection * con,
                   struct ipv4_addr    * remote_addr,
                   struct packet       * pkt)
{
    struct ipv4_pseudo_hdr hdr;
    uint16_t checksum = 0;

    memset(&hdr, 0, sizeof(struct ipv4_pseudo_hdr));

    ipv4_addr_to_octets(con->ipv4_tuple.local_ip,  hdr.src_ip);
    ipv4_addr_to_octets(remote_addr,                    hdr.dst_ip);

    hdr.proto  = IPV4_PROTO_TCP;
    hdr.length = htons(pkt->layer_4_hdr_len + pkt->payload_len);

    checksum = calculate_checksum_begin(&hdr, sizeof(struct ipv4_pseudo_hdr) / 2);
    checksum = calculate_checksum_continue(checksum, pkt->layer_4_hdr, pkt->layer_4_hdr_len / 2);
    checksum = calculate_checksum_continue(checksum, pkt->payload,     pkt->payload_len     / 2);


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

// ok so this is the second step of the three way handshake
// we send a SYN-ACK back to the client in response to their SYN
// this is a helper func for tcp_pkt_rx when we receive a SYN and need to respond with a SYN-ACK
// :(
// vaguely inspired by tcp_listen() and udp_send_datagram()
static int __send_syn_ack(struct tcp_connection * con, struct ipv4_addr * remote_addr, uint16_t remote_port){
    struct packet      * pkt      = NULL;
    struct tcp_raw_hdr * tcp_hdr  = NULL;
    uint16_t             checksum = 0;

    pkt     = create_empty_packet();
    tcp_hdr = __make_tcp_hdr(pkt, 0); // allocate mem inside packet for tcp header

    // fill in tcp header fields
    tcp_hdr->src_port   = htons(con->ipv4_tuple.local_port);
    tcp_hdr->dst_port   = htons(remote_port);
    tcp_hdr->seq_num    = htonl(con->snd_nxt);
    tcp_hdr->ack_num    = htonl(con->rcv_nxt);
    tcp_hdr->header_len = sizeof(struct tcp_raw_hdr) / 4;
    tcp_hdr->flags.SYN  = 1;
    tcp_hdr->flags.ACK  = 1;
    tcp_hdr->recv_win   = htons(65535);
    tcp_hdr->checksum   = 0;

    // synack has no payload
    pkt->payload     = NULL;
    pkt->payload_len = 0;

    // calc checksum
    checksum          = __calculate_chksum(con, remote_addr, pkt);
    tcp_hdr->checksum = checksum;

    if (ipv4_pkt_tx(pkt, remote_addr) != 0) {
        log_error("failed to send syn-ack\n");
        goto err;
    }

    return 0;

err:
    if (pkt) free_packet(pkt);
    return -1;
}


// same as _send_syn_ack, but we are just setting the ack flag, no syn flag. purely acknowedging the recieved data
static int __send_ack(struct tcp_connection * con, struct ipv4_addr * remote_addr, uint16_t remote_port){
    struct packet      * pkt      = NULL;
    struct tcp_raw_hdr * tcp_hdr  = NULL;
    uint16_t             checksum = 0;

    pkt     = create_empty_packet();
    tcp_hdr = __make_tcp_hdr(pkt, 0); // allocate mem inside packet for tcp header

    // fill in tcp header fields
    tcp_hdr->src_port   = htons(con->ipv4_tuple.local_port);
    tcp_hdr->dst_port   = htons(remote_port);
    tcp_hdr->seq_num    = htonl(con->snd_nxt);
    tcp_hdr->ack_num    = htonl(con->rcv_nxt);
    tcp_hdr->header_len = sizeof(struct tcp_raw_hdr) / 4;
    tcp_hdr->flags.ACK  = 1;
    tcp_hdr->recv_win   = htons(65535);
    tcp_hdr->checksum   = 0;

    // synack has no payload
    pkt->payload     = NULL;
    pkt->payload_len = 0;

    // calc checksum
    checksum          = __calculate_chksum(con, remote_addr, pkt);
    tcp_hdr->checksum = checksum;

    if (ipv4_pkt_tx(pkt, remote_addr) != 0) {
        log_error("failed to send ack\n");
        goto err;
    }

    return 0;

err:
    if (pkt) free_packet(pkt);
    return -1;
}

// same as _send_ack, but we are setting the fin flag as well
static int __send_fin_ack(struct tcp_connection * con, struct ipv4_addr * remote_addr, uint16_t remote_port){
    struct packet      * pkt      = NULL;
    struct tcp_raw_hdr * tcp_hdr  = NULL;
    uint16_t             checksum = 0;

    pkt     = create_empty_packet();
    tcp_hdr = __make_tcp_hdr(pkt, 0); // allocate mem inside packet for tcp header

    // fill in tcp header fields
    tcp_hdr->src_port   = htons(con->ipv4_tuple.local_port);
    tcp_hdr->dst_port   = htons(remote_port);
    tcp_hdr->seq_num    = htonl(con->snd_nxt);
    tcp_hdr->ack_num    = htonl(con->rcv_nxt);
    tcp_hdr->header_len = sizeof(struct tcp_raw_hdr) / 4;
    tcp_hdr->flags.ACK  = 1;
    tcp_hdr->flags.FIN  = 1;
    tcp_hdr->recv_win   = htons(65535);
    tcp_hdr->checksum   = 0;

    // synack has no payload
    pkt->payload     = NULL;
    pkt->payload_len = 0;

    // calc checksum
    checksum          = __calculate_chksum(con, remote_addr, pkt);
    tcp_hdr->checksum = checksum;

    if (ipv4_pkt_tx(pkt, remote_addr) != 0) {
        log_error("failed to send fin-ack\n");
        goto err;
    }

    return 0;

err:
    if (pkt) free_packet(pkt);
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

    pet_json_add_u16 (hdr_json, "src port",    ntohs(hdr->src_port));
    pet_json_add_u16 (hdr_json, "dst port",    ntohs(hdr->dst_port));
    pet_json_add_u32 (hdr_json, "seq num",     ntohl(hdr->seq_num));
    pet_json_add_u32 (hdr_json, "ack num",     ntohl(hdr->ack_num));
    pet_json_add_u8  (hdr_json, "header len",  hdr->header_len * 4);
    pet_json_add_bool(hdr_json, "URG flag",    hdr->flags.URG);
    pet_json_add_bool(hdr_json, "ACK flag",    hdr->flags.ACK);
    pet_json_add_bool(hdr_json, "PSH flag",    hdr->flags.PSH);
    pet_json_add_bool(hdr_json, "RST flag",    hdr->flags.RST);
    pet_json_add_bool(hdr_json, "SYN flag",    hdr->flags.SYN);
    pet_json_add_bool(hdr_json, "FIN flag",    hdr->flags.FIN);
    pet_json_add_u16 (hdr_json, "recv win",    ntohs(hdr->recv_win));
    pet_json_add_u16 (hdr_json, "checksum",    ntohs(hdr->checksum));
    pet_json_add_u16 (hdr_json, "urgent ptr",  ntohs(hdr->urgent_ptr));


    return hdr_json;

err:
    if (hdr_json != PET_JSON_INVALID_OBJ) pet_json_free(hdr_json);

    return PET_JSON_INVALID_OBJ;
}


void
print_tcp_header(struct tcp_raw_hdr * tcp_hdr)
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




/*
- when app calls petnet_listen(), petnet eventually calls tcp_listen
- says i am now ready to accept incoming connections on thish port, but does not actually handle any connections
- just sets up the conn and puts it in the LISTEN state, waiting for incoming SYNs
*/
int 
tcp_listen(struct socket    * sock, 
           struct ipv4_addr * local_addr,
           uint16_t           local_port)
{
    struct tcp_state      * tcp_state = petnet_state->tcp_state;
    struct tcp_connection * con       = NULL; // will hold new connection obj
    struct ipv4_addr * remote_ip = ipv4_addr_from_str("0.0.0.0"); // placehold bc we don't know who is connecting yet

    pet_printf("tcp_listen called on port %d\n", local_port);

    // func from tcp_connection that creates a new tcp connection object and adds it to the tcp connection map
    // args: tcp connection map, local ip, remote ip (which is currently unknown), local port, remote port (which is also currently unknown)
    con = create_ipv4_tcp_con(tcp_state->con_map, local_addr, remote_ip, local_port, 0);
    
    // avoid mem leak bc func creates own copy of ip addr we pass in
    free_ipv4_addr(remote_ip);
    remote_ip = NULL;

    // if func above fails, it returns null
    // report err to socket layer
    if (con == NULL) {
        pet_socket_error(sock, EINVAL);
        goto err;
    }

    // link socket ptr to conn obj (so we can look up this conn later using socket ptr in send & close calls)
    add_sock_to_tcp_con(tcp_state->con_map, con, sock);

    con->con_state = LISTEN; // move to listen state
    con->snd_nxt   = 4242; // set rando seq num (FOR NOW)

    // create ipv4 tcp conn func thing returns a LOCKED ref. we must unlock her and release 
    // this bad boy does both
    put_and_unlock_tcp_con(con);
    return 0;

    err:
        // still gotta release
        if (con) put_and_unlock_tcp_con(con);
        return -1;

}

int 
tcp_connect_ipv4(struct socket    * sock, 
                 struct ipv4_addr * local_addr, 
                 uint16_t           local_port,
                 struct ipv4_addr * remote_addr,
                 uint16_t           remote_port)
{
    struct tcp_state      * tcp_state = petnet_state->tcp_state;

    (void)tcp_state; // delete me

    return -1;
}


int
tcp_send(struct socket * sock)
{
    struct tcp_state      * tcp_state = petnet_state->tcp_state;

    (void)tcp_state; // delete me

    return -1;
}



/* Petnet assumes SO_LINGER semantics, so if we'ere here there is no pending write data */
int
tcp_close(struct socket * sock)
{
    struct tcp_state      * tcp_state = petnet_state->tcp_state;
  
    (void)tcp_state; // delete me

    return 0;
}





// aka tcp packet recieve
// called everytime a packet arrives from the network
int 
tcp_pkt_rx(struct packet * pkt)
{
    if (pkt->layer_3_type == IPV4_PKT) {

        struct tcp_state      * tcp_state = petnet_state->tcp_state;
        struct tcp_raw_hdr    * tcp_hdr   = NULL;
        struct ipv4_raw_hdr   * ipv4_hdr  = (struct ipv4_raw_hdr *)pkt->layer_3_hdr;
        struct ipv4_addr      * src_ip    = NULL;
        struct ipv4_addr      * dst_ip    = NULL;
        struct ipv4_addr      * zero_ip   = NULL;
        struct tcp_connection * con       = NULL;
        uint16_t                src_port  = 0;
        uint16_t                dst_port  = 0;

        // get header and payload
        tcp_hdr = __get_tcp_hdr(pkt);
        __get_payload(pkt);

        // extract ips and ports
        src_ip   = ipv4_addr_from_octets(ipv4_hdr->src_ip);
        dst_ip   = ipv4_addr_from_octets(ipv4_hdr->dst_ip);
        src_port = ntohs(tcp_hdr->src_port);
        dst_port = ntohs(tcp_hdr->dst_port);

        pet_printf("TCP packet received!!!!\n");
        print_tcp_header(tcp_hdr);

        zero_ip = ipv4_addr_from_str("0.0.0.0");
        // look up conn in map. note we use dst ip/port bc we are the dest wowowow
        con = get_and_lock_tcp_con_from_ipv4(tcp_state->con_map,
                                             dst_ip,
                                             zero_ip,
                                             dst_port,
                                             0);
        free_ipv4_addr(zero_ip);
        zero_ip = NULL;

        if (con == NULL) {
            log_error("couldn't find TCP connection\n");
            goto out;
        }

        // we r at the heart of the handshake here 

        // if we are in LISTEN state and recieve a SYN:
        //  set rcv_nxt to client's seq num + 1 (bc we expect the next packet from client to have seq num of their initial seq num + 1)
        //  send SYN-ACK back to client (helper func above)
        //  move to SYN_RCVD state (aka we wait for the final ack to complete the handshake)
        if (con->con_state == LISTEN && tcp_hdr->flags.SYN) {
            con->rcv_nxt   = ntohl(tcp_hdr->seq_num) + 1;
            __send_syn_ack(con, src_ip, src_port);
            con->con_state = SYN_RCVD;
            pet_printf("sent SYN-ACK, moving to SYN_RCVD\n");
        }

        // if we are in SYN_RCVD state and receive an ACK
        //  move to ESTABLISHED state (handshake complete!)
        //  increment snd_nxt by 1 to account for the SYN flag we set in our SYN-ACK 
        if (con->con_state == SYN_RCVD && tcp_hdr->flags.ACK) {
            con->snd_nxt   = con->snd_nxt + 1;
            con->con_state = ESTABLISHED;
            pet_socket_accepted(con->sock, src_ip, src_port); // wakes up apps accept call and tells it new conn has arrived
            pet_printf("ACK received, connection ESTABLISHED\n");
        }

        // if we are in ESTABLISHED state and receive data 
        if (con->con_state == ESTABLISHED && pkt->payload_len > 0) {
            con->rcv_nxt = con->rcv_nxt + pkt->payload_len;
            __send_ack(con, src_ip, src_port);
            pet_printf("data received, sent ACK\n");
        }

        // if we are in ESTABLISHED state and receive a FIN
        if (con->con_state == ESTABLISHED && tcp_hdr->flags.FIN) {
            con->rcv_nxt   = con->rcv_nxt + 1;
            __send_fin_ack(con, src_ip, src_port);
            con->snd_nxt   = con->snd_nxt + 1;
            con->con_state = LAST_ACK;
            pet_printf("FIN received, sent FIN-ACK, moving to LAST_ACK\n");
        }

        // if we are in LAST_ACK state and receive an ACK (aka the final ACK of the three way handshake)
        if (con->con_state == LAST_ACK && tcp_hdr->flags.ACK) {
            con->con_state = CLOSED;
            remove_tcp_con(tcp_state->con_map, con);
            pet_socket_closed(con->sock);
            pet_printf("final ACK received, connection CLOSED\n");
        }



// cleanup
out:
        if (con)    put_and_unlock_tcp_con(con);
        if (src_ip) free_ipv4_addr(src_ip);
        if (dst_ip) free_ipv4_addr(dst_ip);
    }

    return 0;
}

int 
tcp_init(struct petnet * petnet_state)
{
    struct tcp_state * state = pet_malloc(sizeof(struct tcp_state));

    state->con_map  = create_tcp_con_map();

    petnet_state->tcp_state = state;
    
    return 0;
}


