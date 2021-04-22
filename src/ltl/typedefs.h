#pragma once

#include <unordered_map>
#include <unordered_set>
#include <set>
#include <vector>
#include <utility>

// some convenience typedefs
typedef std::vector<msat_term> TermList;
typedef std::unordered_map<msat_term, msat_term> TermMap;
typedef std::set<msat_term> TermSet;
typedef std::unordered_set<msat_term> TermHashSet;
typedef std::pair<msat_term, msat_term> TermPair;
typedef std::vector<TermPair> TermPairList;
