#!/usr/bin/env python2
from scapy.all import * # pylint: disable=unused-wildcard-import

payload = """Accept:text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8
Accept-Encoding:gzip, deflate, sdch
Accept-Language:fr-FR,fr;q=0.8,en-US;q=0.6,en;q=0.4,en-GB;q=0.2
Cache-Control:no-cache
Connection:keep-alive
DNT:1
Host:10.0.0.2:8080
Pragma:no-cache
Upgrade-Insecure-Requests:1
User-Agent:Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Ubuntu Chromium/53.0.2785.143 Chrome/53.0.2785.143 Safari/537.36"""

tcp_frame_small = Ether()/IP()/TCP()
udp_frame_small = Ether()/IP()/UDP()
tcp_frame_medium = Ether()/IP()/TCP()
udp_frame_medium = Ether()/IP()/UDP()
arp_frame = Ether()/ARP()

tcp_frame_small[TCP].payload = ""
udp_frame_small[UDP].payload = ""
tcp_frame_medium[TCP].payload = payload
udp_frame_medium[UDP].payload = payload

def sstr(obj):
    return "".join("\\x{}".format(hex(ord(c))[2:].rjust(2, "0")) for c in str(obj))

print("""
let arp_c = Cstruct.of_string "{}"

let ether_c = Cstruct.of_string "{}"

let ip_c = Cstruct.of_string "{}"

let tcp_small_c = Cstruct.of_string "{}"

let udp_small_c = Cstruct.of_string "{}"

let tcp_medium_c = Cstruct.of_string "{}"

let udp_medium_c = Cstruct.of_string "{}"

""").format(sstr(arp_frame[ARP]),
            sstr(tcp_frame_small[Ether]),
            sstr(tcp_frame_small[IP]),
            sstr(tcp_frame_small[TCP]),
            sstr(udp_frame_small[UDP]),
            sstr(tcp_frame_medium[TCP]),
            sstr(udp_frame_medium[UDP]))
