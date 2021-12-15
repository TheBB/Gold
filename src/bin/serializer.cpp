#include <fstream>

#include "gold.hpp"


int main(int argc, char** argv) {
    auto value = Gold::evaluate_file(argv[1]);

    std::fstream fs;
    fs.open(argv[2], std::fstream::out);
    value.serialize(fs);
    fs.close();

    return 0;
}
