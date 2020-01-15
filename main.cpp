#include <iostream>
#include <fstream>
#include <sstream>

#include "policy.h"
#include "parser.h"

using namespace std;

djn_pubkey_t* pub;
djn_prvkey_t* prv;

StringSet split_line(const String& line)
{
    String part;
    String substring = line;
    StringSet parts;
    size_t pos = 0;

    while ((pos = substring.find("===")) != std::string::npos) {
        part = substring.substr(0, pos);
        parts.push_back(part);
        substring.erase(0, pos + 3);
    }

    parts.push_back(substring);
    return parts;
}

int main()
{
	unsigned int bandwidth = 0;

	pub = (djn_pubkey_t*) malloc(1);
	prv = (djn_prvkey_t*) malloc(1);
	djn_keygen(1024, &pub, &prv);

	mpz_t t, f, u, t_output, f_output, u_output, n_minus_1;
	mpz_inits(t, f, u, n_minus_1, NULL);
    mpz_sub_ui(n_minus_1, pub->n, 1);

    std::ifstream input("data/experiment.txt");
    int number = 0;

    String line;

    while(std::getline(input, line)) {
        if(!line.empty()) {
            if (line.substr(0, 1) != "#") {
                number += 1;

                StringSet parts = split_line(line);
                String index = parts[0];
                Query query = perform_query_parsing(pub, parts[1]);
                //std::cout << "query parsed...";
                Node* policy = perform_policy_parsing(pub, parts[2]);

//std::cout << "Evaluation started on policy " << number << "..." << std::endl;

                policy->evaluate(t, f, u, pub, prv, n_minus_1, query);

                djn_decrypt(t_output, pub, prv, t);
                djn_decrypt(f_output, pub, prv, f);
                djn_decrypt(u_output, pub, prv, u);

                std::cout << index;
                gmp_printf("===[%Zd,%Zd,%Zd]===", t_output, f_output, u_output);
                printf("[%f]===[%d]\n", policy->timeSpent / 1000, policy->bandwidth / 8);
            }
        }
    }

    input.close();
    /*
	mpz_t a, b, ae, be, zero, one, four, five, ten, fivety, ninetytwo, enc_0, enc_4, enc_5, enc_10, enc_50, enc_92, n_minus_1;
	mpz_inits(a, b, ae, be, zero, one, four, five, ten, fivety, ninetytwo, enc_0, enc_4, enc_5, enc_10, enc_50, enc_92, n_minus_1, NULL);
	mpz_set_ui(zero, 0);
	mpz_set_ui(four, 4);
	mpz_set_ui(five, 5);
	mpz_set_ui(ten, 10);
    mpz_set_ui(fivety, 50);
    mpz_set_ui(ninetytwo, 92);
    mpz_set_ui(a, 6);
    mpz_set_ui(b, 7);
    mpz_sub_ui(n_minus_1, pub->n, 1);

    // Encryption
    djn_encrypt(enc_0, pub, zero);
    djn_encrypt(enc_4, pub, four);
    djn_encrypt(enc_92, pub, ninetytwo);
    djn_encrypt(enc_10, pub, ten);
    djn_encrypt(enc_5, pub, one);
    djn_encrypt(enc_50, pub, fivety);
    djn_encrypt(ae, pub, a);
    djn_encrypt(be, pub, b);

	cout << "Making policy..." << endl;

	Node *policy = new Target(
        &enc_10,
        &enc_92,
        &enc_4,
        new Leaf(&enc_0)
    );

	Pair p;
	p.attribute = &enc_5;
	p.value = &enc_50;
    Pair p2;
    p2.attribute = &ae;
    p2.value = &be;
	Query q;
	q.push_back(p);
    q.push_back(p2);

	cout << "Starting evaluation..." << endl;

	mpz_t res_t, res_f, res_u, t, f, u;
	mpz_inits(res_t, res_f, res_u, t, f, u, NULL);

	policy->evaluate(res_t, res_f, res_u, pub, prv, n_minus_1, q);

	cout << "Output" << endl;

	djn_decrypt(t, pub, prv, res_t);
	djn_decrypt(u, pub, prv, res_u);
	djn_decrypt(f, pub, prv, res_f);

	cout << "Decrypted output" << endl;
	gmp_printf("t: %Zd, f: %Zd, u: %Zd", t, f, u);
    */
	return 0;
}
