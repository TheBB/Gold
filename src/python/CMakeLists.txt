pybind11_add_module(pygold ${CMAKE_CURRENT_SOURCE_DIR}/main.cpp)

target_link_libraries(pygold PRIVATE gold-nostdlib gold-stdlib)
