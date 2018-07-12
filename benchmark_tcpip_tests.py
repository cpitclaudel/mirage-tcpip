#!/usr/bin/env python3
import subprocess
import time
import statistics

SUPPORTED = ["ethif", "arpv4", "ipv4", "tcp", "udp"]
CONFIG_ALL = " ".join(p for prot in SUPPORTED for p in [prot + "-encoding", prot + "-decoding"])
CONFIGS = ("mirage", ""), ("fiat", CONFIG_ALL)
NREPEATS = 3

TESTS = [
    "arp-dec",
    "ether-dec",
    "ip-enc", "ip-dec",
    "tcp-dec",
    "udp-dec"
]


def benchmark(config_name, config):
    with open("/tmp/fiat4mirage.config", mode="w") as out:
        out.write(config + "\n")

    for test_id, test_name in enumerate(TESTS):
        for repeat in range(NREPEATS):
            start = time.time()
            subprocess.check_call(["_build/default/test/test.exe", "test", "tight_loop", str(test_id)],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            end = time.time()
            yield test_name, (end - start)

def main():
    results = {}
    for config_name, config in CONFIGS:
        print("\n# Benchmarking {}...".format(config))
        for test_name, elapsed in benchmark(config_name, config):
            results.setdefault(test_name, {}).setdefault(config_name, []).append(elapsed)
            print(">>\t{}\t{}\t{:.5f}".format(config_name, test_name, elapsed))

    print("\n# Relative slowdown:")
    for test, subresults in results.items():
        means = {config_name: statistics.mean(timings)
                 for config_name, timings in subresults.items()}
        print(">>\t{}\t{}/{}\t{:.5f}".format(test, "fiat", "mirage", means["fiat"] / means["mirage"]))

    from pprint import pprint
    pprint(results)


if __name__ == '__main__':
    main()
