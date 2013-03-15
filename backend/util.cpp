#include "util.hpp"

namespace util {

  std::string string_of_error_code(error_code ec)
  {
    switch (ec) {
    case ec_type:
      return string("TYPE");
    case ec_syntax:
      return string("SYNTAX");
    case ec_backend:
      return string("BACKEND");
    case ec_id:
      return string("ID");
    case ec_case:
      return string("CASE");
    case ec_api:
      return string("API");
    case ec_interrupted:
      return string("INTERRUPTED");
    case ec_logic:
      return string("LOGIC");
    case ec_type_uf:
      return string("TYPE_UF");
    case ec_unimplemented:
      return string("UNIMPLEMENTED");
    case ec_sanity:
      return string("SANITY");
    default:
      return string("UNKNOWN");
    }
  }

}
