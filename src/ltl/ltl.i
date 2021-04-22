%module ltl

%include "std_unordered_map.i"
%include "std_vector.i"
%include "std_pair.i"

%import(module="mathsat") "../../venv/include/mathsat.h"

%{
  #include "ts.h"
  #include "ltl.h"
  #define SWIG_FILE_WITH_INIT
%}

%template(TermList) std::vector<msat_term>;
%template(TermPair) std::pair<msat_term, msat_term>;
%template(TermPairList) std::vector<std::pair<msat_term, msat_term> >;
%template(TermMap) std::unordered_map<msat_term, msat_term>;

%include "typedefs.h"
%include "opts.h"
%include "ts.h"
%include "ltl.h"
