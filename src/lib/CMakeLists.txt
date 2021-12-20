add_library(
    gold-nostdlib
    ${CMAKE_CURRENT_SOURCE_DIR}/gold.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/parsing.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/serialization.cpp
)

add_library(
    gold-stdlib OBJECT
    ${CMAKE_CURRENT_SOURCE_DIR}/stdlib.cpp
)

target_include_directories(gold-nostdlib PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/include)
