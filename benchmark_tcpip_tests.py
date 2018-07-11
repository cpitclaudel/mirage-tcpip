#!/usr/bin/env python3
import subprocess
import time

CONFIGS = "", "ethif arpv4 ipv4 tcp udp"
NREPEATS = 3

TESTS = ["arp", "ether", "ip", "tcp", "udp"]

def benchmark(config):
    with open("config.fiat4mirage", mode="w") as out:
        out.write(config + "\n")

    for test_id, test_name in enumerate(TESTS):
        for repeat in range(NREPEATS):
            start = time.time()
            subprocess.check_call(["_build/test/test.native", "test", "tight_loop", str(test_id)],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            end = time.time()
            print(">>\t{}\t{}\t{:.5f}".format(config, test_name, end-start))

def main():
    for config in CONFIGS:
        print("\n# Benchmarking {}...".format(config))
        benchmark(config)

if __name__ == '__main__':
    main()
