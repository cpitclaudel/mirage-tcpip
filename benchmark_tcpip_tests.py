#!/usr/bin/env python3
import subprocess
import time
import statistics

# Build ‘test.exe’ with ‘jbuilder runtest --dev --force --verbose’ before
# running this

SUPPORTED = ["ethif", "arpv4", "ipv4", "tcp", "udp"]
CONFIG_ALL = " ".join(p for prot in SUPPORTED for p in [prot + "-encoding", prot + "-decoding"])
CONFIGS = ("mirage", ""), ("fiat", CONFIG_ALL)
NREPEATS = 3

TESTS = [
    "arp-dec",
    "ether-dec",
    "ipv4-enc",
    "ipv4-dec",
    "tcp-enc-s",
    "tcp-dec-s",
    "udp-enc-s",
    "udp-dec-s",
    "tcp-enc-m",
    "tcp-dec-m",
    "udp-enc-m",
    "udp-dec-m",
]

def benchmark(_config_name, config):
    with open("/tmp/fiat4mirage.config", mode="w") as out:
        out.write(config + "\n")

    for test_id, test_name in enumerate(TESTS):
        for _repeat in range(NREPEATS):
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
    for test in TESTS:
        subresults = results[test]
        means = {config_name: statistics.mean(timings)
                 for config_name, timings in subresults.items()}
        print(">>\t{}\t{}/{}\t{:.5f}".format(test, "fiat", "mirage", means["fiat"] / means["mirage"]))

    from pprint import pprint
    pprint(results)


if __name__ == '__main__':
    main()
