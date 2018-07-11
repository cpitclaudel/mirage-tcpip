#!/usr/bin/env python2
from scapy.all import *

large = """Accept:text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8
Accept-Encoding:gzip, deflate, sdch
Accept-Language:fr-FR,fr;q=0.8,en-US;q=0.6,en;q=0.4,en-GB;q=0.2
Cache-Control:no-cache
Connection:keep-alive
DNT:1
Host:10.0.0.2:8080
Pragma:no-cache
Upgrade-Insecure-Requests:1
User-Agent:Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Ubuntu Chromium/53.0.2785.143 Chrome/53.0.2785.143 Safari/537.36"""

payload = ""

tcp_frame = Ether()/IP()/TCP()
udp_frame = Ether()/IP()/UDP()
arp_frame = Ether()/ARP()

tcp_frame[TCP].payload = payload
udp_frame[UDP].payload = payload

def sstr(obj):
    return "".join("\\x{}".format(hex(ord(c))[2:].rjust(2, "0")) for c in str(obj))

print("""
let arp_c = Cstruct.of_string "{}"

let ether_c = Cstruct.of_string "{}"

let ip_c = Cstruct.of_string "{}"

let tcp_c = Cstruct.of_string "{}"

let udp_c = Cstruct.of_string "{}"

""").format(sstr(arp_frame[ARP]),
            sstr(tcp_frame[Ether]),
            sstr(tcp_frame[IP]),
            sstr(tcp_frame[TCP]),
            sstr(udp_frame[UDP]))
