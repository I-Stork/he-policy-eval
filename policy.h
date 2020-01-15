#ifndef __POLICY_H_
#define __POLICY_H_

#include <cassert>
#include <cmath>
#include <iostream>
#include <vector>
#include "gmp.h"
#include "djn.h"
#include "utils.h"

typedef std::vector<mpz_t*> CipherSet;

struct Pair
{
    mpz_t attribute;
    mpz_t value;
};

typedef std::vector<Pair> Query;

enum CombinationRule { NOT, WEA, SMAX, SMIN, WMAX, WMIN, PO, DO, FA };

class Node {
public:
    Node *child1;
    Node *child2;

	double timeSpent = 0;
	unsigned int bandwidth = 0;

    Node(Node *c1, Node *c2)
        : child1(c1), child2(c2)
    {
    }

    virtual void evaluate(mpz_t t, mpz_t f, mpz_t u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1, Query q)
    {
    }

    double getMillies(timespec timestart, timespec timeend);
    int NchooseK(int n, int k);
    void PolyCoeffGen(mpz_t coeff[], djn_pubkey_t* pub, int logL);

    CipherSet QueryAttributes(Query& q);

    void SecureEqualityProtocol(mpz_t res, mpz_t a, mpz_t b, djn_pubkey_t* pub, djn_prvkey_t* prv);
    void SecureComparisonProtocol(mpz_t res, mpz_t a, mpz_t b, djn_pubkey_t* pub, djn_prvkey_t* prv);
    void SecureMultiplicationProtocol(mpz_t res, mpz_t a, mpz_t b, djn_pubkey_t* pub, djn_prvkey_t* prv);

	void SNP(mpz_t res, mpz_t a, djn_pubkey_t* pub, mpz_t n_minus_1);
	void SDP(mpz_t res, mpz_t a, mpz_t b, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1);
	void SCP(mpz_t res, mpz_t a, mpz_t b, djn_pubkey_t* pub, djn_prvkey_t* prv);

    void Not(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1);
    void wea(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1);
    void smax(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, mpz_t t2_t, mpz_t t2_f, mpz_t t2_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1);
    void smin(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, mpz_t t2_t, mpz_t t2_f, mpz_t t2_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1);
    void wmax(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, mpz_t t2_t, mpz_t t2_f, mpz_t t2_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1);
    void wmin(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, mpz_t t2_t, mpz_t t2_f, mpz_t t2_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1);
    void po(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, mpz_t t2_t, mpz_t t2_f, mpz_t t2_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1);
    void Do(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, mpz_t t2_t, mpz_t t2_f, mpz_t t2_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1);
    void fa(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, mpz_t t2_t, mpz_t t2_f, mpz_t t2_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1);
};

class Target : public Node
{
public:
    mpz_t attribute;
    mpz_t value;
    mpz_t condition;

    Target(mpz_t a, mpz_t v, mpz_t c, Node *c1)
        : Node(c1, NULL)
    {
        mpz_inits(attribute, value, condition, NULL);

        mpz_set(attribute, a);
        mpz_set(value, v);
        mpz_set(condition, c);
    }

    void evaluate(mpz_t t, mpz_t f, mpz_t u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1, Query q);
    void target_evaluate(mpz_t t, mpz_t f, mpz_t u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1, Query q);

};

class DummyTarget : public Node
{
public:
	mpz_t t;
    mpz_t f;
    mpz_t u;


	DummyTarget(mpz_t enc_t, mpz_t enc_f, mpz_t enc_u)
		: Node(NULL, NULL)
	{
        mpz_inits(t, f, u, NULL);

        mpz_set(t, enc_t);
        mpz_set(f, enc_f);
        mpz_set(u, enc_u);
	}

    void evaluate(mpz_t t, mpz_t f, mpz_t u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1, Query q);

};

class Leaf: public Node
{
public:
    mpz_t value;

    Leaf(mpz_t val)
        : Node(NULL, NULL)
    {
        mpz_init(value);
        mpz_set(value, val);
    }

    void evaluate(mpz_t t, mpz_t f, mpz_t u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1, Query q);

};

class Operation: public Node
{
public:
    CombinationRule rule;

    Operation(CombinationRule r, Node *c1, Node *c2)
        : Node(c1, c2), rule(r)
    {
    }
    Operation(CombinationRule r, Node *c1)
        : Node(c1, NULL), rule(r)
    {
    }

    void evaluate(mpz_t t, mpz_t f, mpz_t u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1, Query q);

};

#endif /* __POLICY_H_ */
