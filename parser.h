#ifndef __PARSER_H_
#define __PARSER_H_

#include "policy.h"

typedef std::string String;
typedef std::vector<String> StringSet;

StringSet split_parsing(const String& line);
Node* leaf_parsing(djn_pubkey_t* pub, const String& line);
Node* dummy_target_parsing(djn_pubkey_t* pub, String line);
Node* target_parsing(djn_pubkey_t* pub, String line);
Node* operation_parsing(djn_pubkey_t* pub, String line);
Node* policy_parsing(djn_pubkey_t* pub, const String &line);
Node* perform_policy_parsing(djn_pubkey_t* pub, const String& line);
StringSet split_query(const String& line);
Query perform_query_parsing(djn_pubkey_t* pub, String line);

#endif /* __PARSER_H_ */
