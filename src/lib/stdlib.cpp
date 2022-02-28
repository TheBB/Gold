#include <iostream>

#include "gold.hpp"

#include "std.gold.serialized.c"


using namespace Gold;


#define STDLIB(name) {#name, std::string((char*)name ## _gold_serialized, name ## _gold_serialized_len)}

static std::map<std::string, std::string> stdlibs = {
    STDLIB(std),
};


class StdlibFinder: public LibFinder {
public:
    virtual opt<Object> find(const std::string& path) const {
        if (stdlibs.find(path) == stdlibs.end())
            return opt<Object>();
        return Object::deserialize(stdlibs[path]);
    }
};


bool startup() {
    register_stdlib(std::make_unique<StdlibFinder>());
    return true;
}

bool _ = startup();
