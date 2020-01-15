#include "parser.h"

StringSet split_parsing(const String& line)
{
    String part;
    int open = 0;
    StringSet parts;

    for (int i = 0; i < line.length(); i++){
        if (line.substr(i, 1) == "("){
            open += 1;
            part += line.substr(i, 1);
        } else if (line.substr(i, 1) == ")") {
            open -= 1;
            part += line.substr(i, 1);
        } else if (line.substr(i, 1) == " " && open == 0){

        } else if (line.substr(i, 1) == "," && open == 0){
            parts.push_back(part);
            part = "";
        } else {
            part += line.substr(i, 1);
        }
    }

    parts.push_back(part);

    return parts;
}

Node* leaf_parsing(djn_pubkey_t* pub, const String& line) {
    int val = std::stoi(line.substr(1,1));
    mpz_t value, enc_value;
    mpz_inits(value, enc_value);
    mpz_set_ui(value, val);
    djn_encrypt(enc_value, pub, value);
    Node *leaf = new Leaf(enc_value);
    return leaf;
}

Node* dummy_target_parsing(djn_pubkey_t* pub, String line) {
	Node *dummy_target;

    line = line.substr(2, line.length() - 3);
    StringSet parts = split_parsing(line);

    mpz_t plain_t, plain_f, plain_u, enc_t, enc_f, enc_u;
    mpz_inits(plain_t, plain_f, plain_u, enc_t, enc_f, enc_u, NULL);

    uint32_t t = std::stoi(parts[0]);
    uint32_t f = std::stoi(parts[1]);
    uint32_t u = std::stoi(parts[2]);

    mpz_set_ui(plain_t, t);
    mpz_set_ui(plain_f, f);
    mpz_set_ui(plain_u, u);

    djn_encrypt(enc_t, pub, plain_t);
    djn_encrypt(enc_f, pub, plain_f);
    djn_encrypt(enc_u, pub, plain_u);

    dummy_target = new DummyTarget(enc_t, enc_f, enc_u);

	return dummy_target;
}

Node* target_parsing(djn_pubkey_t* pub, String line) {
    Node *target;

    line = line.substr(2, line.length() - 3);
    StringSet parts = split_parsing(line);

    mpz_t attr, value, cond, enc_a, enc_v, enc_c;
    mpz_inits(attr, value, cond, enc_a, enc_v, enc_c, NULL);

    int a = std::stoi(parts[0]);
    int v = std::stoi(parts[1]);
    int c = std::stoi(parts[2]);
    mpz_set_ui(attr, a);
    mpz_set_ui(value, v);
    mpz_set_ui(cond, c);
    djn_encrypt(enc_a, pub, attr);
    djn_encrypt(enc_v, pub, value);
    djn_encrypt(enc_c, pub, cond);

    String line1 = parts[3].substr(1, parts[3].length() - 2);
    Node *child1 = policy_parsing(pub, line1);
    target = new Target(enc_a, enc_v, enc_c, child1);

    return target;
}

Node* operation_parsing(djn_pubkey_t* pub, String line) {
    Node *operation;

    if (line.substr(0, 4) == "not(") {
        line = line.substr(4, line.length() - 5);
        String line1 = line.substr(1, line.length() - 2);
        Node *child1 = policy_parsing(pub, line1);

        operation = new Operation(NOT, child1);
    } else if (line.substr(0, 4) == "wea(") {
        line = line.substr(4, line.length() - 5);
        String line1 = line.substr(1, line.length() - 2);
        Node *child1 = policy_parsing(pub, line1);

        operation = new Operation(WEA, child1);
    } else if (line.substr(0, 5) == "smax(") {
        line = line.substr(5, line.length() - 6);
        StringSet parts = split_parsing(line);
        String line1 = parts[0].substr(1, parts[0].length() - 2);
        String line2 = parts[1].substr(1, parts[1].length() - 2);
        Node *child1 = policy_parsing(pub, line1);
        Node *child2 = policy_parsing(pub, line2);

        operation = new Operation(SMAX, child1, child2);
    } else if (line.substr(0, 5) == "smin(") {
        line = line.substr(5, line.length() - 6);
        StringSet parts = split_parsing(line);
        String line1 = parts[0].substr(1, parts[0].length() - 2);
        String line2 = parts[1].substr(1, parts[1].length() - 2);
        Node *child1 = policy_parsing(pub, line1);
        Node *child2 = policy_parsing(pub, line2);

        operation = new Operation(SMIN, child1, child2);
    } else if (line.substr(0, 5) == "wmax(") {
        line = line.substr(5, line.length() - 6);
        StringSet parts = split_parsing(line);
        String line1 = parts[0].substr(1, parts[0].length() - 2);
        String line2 = parts[1].substr(1, parts[1].length() - 2);
        Node *child1 = policy_parsing(pub, line1);
        Node *child2 = policy_parsing(pub, line2);

        operation = new Operation(WMAX, child1, child2);
    } else if (line.substr(0, 5) == "wmin(") {
        line = line.substr(5, line.length() - 6);
        StringSet parts = split_parsing(line);
        String line1 = parts[0].substr(1, parts[0].length() - 2);
        String line2 = parts[1].substr(1, parts[1].length() - 2);
        Node *child1 = policy_parsing(pub, line1);
        Node *child2 = policy_parsing(pub, line2);

        operation = new Operation(WMIN, child1, child2);
    } else if (line.substr(0, 3) == "po(") {
        line = line.substr(3, line.length() - 4);
        StringSet parts = split_parsing(line);
        String line1 = parts[0].substr(1, parts[0].length() - 2);
        String line2 = parts[1].substr(1, parts[1].length() - 2);
        Node *child1 = policy_parsing(pub, line1);
        Node *child2 = policy_parsing(pub, line2);

        operation = new Operation(PO, child1, child2);
    } else if (line.substr(0, 3) == "do(") {
        line = line.substr(3, line.length() - 4);
        StringSet parts = split_parsing(line);
        String line1 = parts[0].substr(1, parts[0].length() - 2);
        String line2 = parts[1].substr(1, parts[1].length() - 2);
        Node *child1 = policy_parsing(pub, line1);
        Node *child2 = policy_parsing(pub, line2);

        operation = new Operation(DO, child1, child2);
    } else if (line.substr(0, 3) == "fa(") {
        line = line.substr(3, line.length() - 4);
        StringSet parts = split_parsing(line);
        String line1 = parts[0].substr(1, parts[0].length() - 2);
        String line2 = parts[1].substr(1, parts[1].length() - 2);
        Node *child1 = policy_parsing(pub, line1);
        Node *child2 = policy_parsing(pub, line2);

        operation = new Operation(FA, child1, child2);
    }

    return operation;
}

Node* policy_parsing(djn_pubkey_t* pub, const String& line) {
    Node *policy;

    if (line.substr(0, 1) == "[") {
        policy = leaf_parsing(pub, line);
    } else if (line.substr(0, 1) == "T") {
        policy = target_parsing(pub, line);
	} else if (line.substr(0, 1) == "D") {
		policy = dummy_target_parsing(pub, line);
    } else {
        policy = operation_parsing(pub, line);
    }

    return policy;
}

Node* perform_policy_parsing(djn_pubkey_t* pub, const String& line){
    String substring = line.substr(1, line.length() - 2);
    Node* policy = policy_parsing(pub, substring);
    return policy;
}

StringSet split_query(const String& line)
{
    String part;
    String substring = line;
    StringSet parts;
    size_t pos = 0;

    while ((pos = substring.find("}, {")) != std::string::npos) {
        part = substring.substr(0, pos);
        parts.push_back(part);
        substring.erase(0, pos + 4);
    }

    parts.push_back(substring);
    return parts;
}

Query perform_query_parsing(djn_pubkey_t* pub, String line){
    Query query;
    line = line.substr(2, line.length() - 4);
    StringSet parts = split_query(line);
    mpz_t attr, val, attr_enc, val_enc;
    mpz_inits(attr, val, attr_enc, val_enc, NULL);

    for (int i = 0; i < parts.size(); i++){
        StringSet numbers = split_parsing(parts[i]);
        int a = std::stoi(numbers[0]);
        int v = std::stoi(numbers[1]);

        mpz_set_ui(attr, a);
        mpz_set_ui(val, v);

        djn_encrypt(attr_enc, pub, attr);
        djn_encrypt(val_enc, pub, val);
        Pair p;
        mpz_inits(p.attribute, p.value, NULL);
        mpz_set(p.attribute, attr_enc);
        mpz_set(p.value, val_enc);
        query.push_back(p);
    }

    return query;
}
