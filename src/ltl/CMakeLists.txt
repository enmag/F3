cmake_minimum_required(VERSION 2.8)
project(ltl)


find_package(SWIG REQUIRED)
include(${SWIG_USE_FILE})

find_package(PythonLibs)
include_directories(${PYTHON_INCLUDE_PATH})

include_directories(${CMAKE_CURRENT_SOURCE_DIR})

set(CMAKE_SWIG_FLAGS "")

set_source_files_properties(ltl.i PROPERTIES CPLUSPLUS ON)
set_source_files_properties(ltl.i PROPERTIES SWIG_FLAGS "-includeall")
swig_add_library(ltl LANGUAGE python SOURCES ltl.i ltl.cpp)
swig_link_libraries(ltl ${PYTHON_LIBRARIES})



# set(MATHSAT_DIR "" CACHE PATH "directory of MathSAT")
# set(MSAT_INCLUDE_DIR "" CACHE PATH "include dir for mathsat")
# set(MSAT_LIB_DIR "" CACHE PATH "library dir for mathsat")

# if(MATHSAT_DIR)
#     set(MSAT_LIB_DIR "${MATHSAT_DIR}/lib" CACHE INTERNAL "")
#     set(MSAT_INCLUDE_DIR "${MATHSAT_DIR}/include" CACHE INTERNAL "")
# endif()

# find_library(mathsat mathsat PATHS "${MSAT_LIB_DIR}")
# if(NOT mathsat)
#     message(FATAL_ERROR "mathsat not found in ${MSAT_LIB_DIR}")
# endif()

find_library(gmp gmp)
find_library(gmpxx gmpxx)
find_library(mathsat mathsat)

set(SRCS
    utils.cpp
    ts.cpp
    ltl.cpp
    )

include_directories(. ${MSAT_INCLUDE_DIR})

add_definitions(-std=c++17)
add_library(ltl ${SRCS})
# set_target_properties(ltl_main PROPERTIES OUTPUT_NAME ltl)
# target_link_libraries(ltl_main ltl ${mathsat} ${gmp} ${gmpxx})
