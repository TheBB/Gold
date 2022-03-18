#include "catch.hpp"

#include <fmt/core.h>

#include "gold.hpp"

using Catch::Matchers::Contains;
using namespace Gold;


TEST_CASE("dh-books", "[examples]") {
    auto obj = evaluate_file(GOLD_EXAMPLES_DIR "/dh-books.gold");
    REQUIRE(obj.size() == 3);
    REQUIRE(obj[0]["publisher"].unsafe_string() == "O'Reilly Media");
    REQUIRE(obj[1]["publisher"].unsafe_string() == "Addison Wesley");
    REQUIRE(obj[2]["publisher"].unsafe_string() == "O'Reilly Media");
    REQUIRE(obj[0]["title"].unsafe_string() == "Microservices for Java Developers");
    REQUIRE(obj[1]["title"].unsafe_string() == "The Go Programming Language");
    REQUIRE(obj[2]["title"].unsafe_string() == "Parallel and Concurrent Programming in Haskell");
}


TEST_CASE("dh-definitions", "[examples]") {
    auto files = {GOLD_EXAMPLES_DIR "/dh-definitions.gold", GOLD_EXAMPLES_DIR "/dh-hello-world.gold"};
    for (auto fn : files) {
        auto obj = evaluate_file(fn);
        REQUIRE(obj.size() == 3);
        REQUIRE(obj["home"].unsafe_string() == "/home/bill");
        REQUIRE(obj["privateKey"].unsafe_string() == "/home/bill/.ssh/id_ed25519");
        REQUIRE(obj["publicKey"].unsafe_string() == "/home/bill/.ssh/id_ed25519.pub");
    }
}


TEST_CASE("dh-employees", "[examples]") {
    auto obj = evaluate_file(GOLD_EXAMPLES_DIR "/dh-employees.gold");
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0]["age"].unsafe_integer() == 23);
    REQUIRE(obj[0]["name"].unsafe_string() == "John Doe");
    REQUIRE(obj[0]["position"]["department"].unsafe_string() == "Data Platform");
    REQUIRE(obj[0]["position"]["title"].unsafe_string() == "Software Engineer");
    REQUIRE(obj[1]["age"].unsafe_integer() == 24);
    REQUIRE(obj[1]["name"].unsafe_string() == "Alice Smith");
    REQUIRE(obj[1]["position"]["department"].unsafe_string() == "Data Platform");
    REQUIRE(obj[1]["position"]["title"].unsafe_string() == "Software Engineer");
}


TEST_CASE("dh-filter", "[examples]") {
    auto files = {GOLD_EXAMPLES_DIR "/dh-filter.gold", GOLD_EXAMPLES_DIR "/dh-filter-import.gold"};
    for (auto fn : files) {
        auto obj = evaluate_file(fn);
        REQUIRE(obj.size() == 2);
        REQUIRE(obj[0]["name"].unsafe_string() == "Alice");
        REQUIRE(obj[0]["age"].unsafe_integer() == 24);
        REQUIRE(obj[0]["admin"].unsafe_boolean());
        REQUIRE(obj[1]["name"].unsafe_string() == "Bob");
        REQUIRE(obj[1]["age"].unsafe_integer() == 49);
        REQUIRE(obj[1]["admin"].unsafe_boolean());
    }
}


TEST_CASE("dh-functions", "[examples]") {
    auto obj = evaluate_file(GOLD_EXAMPLES_DIR "/dh-functions.gold");
    REQUIRE(obj.size() == 2);
    REQUIRE(obj[0]["home"].unsafe_string() == "/home/bill");
    REQUIRE(obj[0]["privateKey"].unsafe_string() == "/home/bill/.ssh/id_ed25519");
    REQUIRE(obj[0]["publicKey"].unsafe_string() == "/home/bill/.ssh/id_ed25519.pub");
    REQUIRE(obj[1]["home"].unsafe_string() == "/home/jane");
    REQUIRE(obj[1]["privateKey"].unsafe_string() == "/home/jane/.ssh/id_ed25519");
    REQUIRE(obj[1]["publicKey"].unsafe_string() == "/home/jane/.ssh/id_ed25519.pub");
}


TEST_CASE("dh-generate", "[examples]") {
    auto obj = evaluate_file(GOLD_EXAMPLES_DIR "/dh-generate.gold");
    REQUIRE(obj.size() == 10);
    for (int i = 0; i < 10; i++) {
        REQUIRE(obj[i]["home"].unsafe_string() == fmt::format("/home/build{}", i));
        REQUIRE(obj[i]["privateKey"].unsafe_string() == fmt::format("/home/build{}/.ssh/id_ed25519", i));
        REQUIRE(obj[i]["publicKey"].unsafe_string() == fmt::format("/home/build{}/.ssh/id_ed25519.pub", i));
    }
}


TEST_CASE("dh-servers", "[examples]") {
    auto files = {GOLD_EXAMPLES_DIR "/dh-servers.gold", GOLD_EXAMPLES_DIR "/dh-servers-2.gold"};
    for (auto fn : files) {
        auto obj = evaluate_file(fn);
        REQUIRE(obj.size() == 6);
        REQUIRE(obj[0]["cpus"].unsafe_integer() == 1);
        REQUIRE(obj[0]["gigabytesOfRAM"].unsafe_integer() == 1);
        REQUIRE(obj[0]["terabytesOfDisk"].unsafe_integer() == 1);
        REQUIRE(obj[0]["hostname"].unsafe_string() == "eu-west.example.com");
        REQUIRE(obj[1]["cpus"].unsafe_integer() == 64);
        REQUIRE(obj[1]["gigabytesOfRAM"].unsafe_integer() == 256);
        REQUIRE(obj[1]["terabytesOfDisk"].unsafe_integer() == 16);
        REQUIRE(obj[1]["hostname"].unsafe_string() == "us-east.example.com");
        REQUIRE(obj[2]["cpus"].unsafe_integer() == 64);
        REQUIRE(obj[2]["gigabytesOfRAM"].unsafe_integer() == 256);
        REQUIRE(obj[2]["terabytesOfDisk"].unsafe_integer() == 16);
        REQUIRE(obj[2]["hostname"].unsafe_string() == "ap-northeast.example.com");
        REQUIRE(obj[3]["cpus"].unsafe_integer() == 8);
        REQUIRE(obj[3]["gigabytesOfRAM"].unsafe_integer() == 16);
        REQUIRE(obj[3]["terabytesOfDisk"].unsafe_integer() == 4);
        REQUIRE(obj[3]["hostname"].unsafe_string() == "us-west.example.com");
        REQUIRE(obj[4]["cpus"].unsafe_integer() == 1);
        REQUIRE(obj[4]["gigabytesOfRAM"].unsafe_integer() == 1);
        REQUIRE(obj[4]["terabytesOfDisk"].unsafe_integer() == 1);
        REQUIRE(obj[4]["hostname"].unsafe_string() == "sa-east.example.com");
        REQUIRE(obj[5]["cpus"].unsafe_integer() == 64);
        REQUIRE(obj[5]["gigabytesOfRAM"].unsafe_integer() == 256);
        REQUIRE(obj[5]["terabytesOfDisk"].unsafe_integer() == 16);
        REQUIRE(obj[5]["hostname"].unsafe_string() == "ca-central.example.com");
    }
}


TEST_CASE("dh-users", "[examples]") {
    auto obj = evaluate_file(GOLD_EXAMPLES_DIR "/dh-users.gold");
    REQUIRE(obj.size() == 3);
    REQUIRE(obj[0]["name"].unsafe_string() == "Alice");
    REQUIRE(obj[0]["age"].unsafe_integer() == 24);
    REQUIRE(obj[0]["admin"].unsafe_boolean());
    REQUIRE(obj[1]["name"].unsafe_string() == "Bob");
    REQUIRE(obj[1]["age"].unsafe_integer() == 49);
    REQUIRE(obj[1]["admin"].unsafe_boolean());
    REQUIRE(obj[2]["name"].unsafe_string() == "Carlo");
    REQUIRE(obj[2]["age"].unsafe_integer() == 20);
    REQUIRE(!obj[2]["admin"].unsafe_boolean());
}


TEST_CASE("fibonacci", "[examples]") {
    auto obj = evaluate_file(GOLD_EXAMPLES_DIR "/fibonacci.gold");
    REQUIRE(obj.unsafe_integer() == 13);
}
