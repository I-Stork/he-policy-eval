#include "policy.h"

struct timespec startT, endT;

/*
 * Combination rules
 */

double Node::getMillies(timespec timestart, timespec timeend)
{
	long time1 = (timestart.tv_sec * 1000000) + (timestart.tv_nsec / 1000);
    long time2 = (timeend.tv_sec * 1000000) + (timeend.tv_nsec / 1000);

    return (double) (time2 - time1) / 1000;
}

/*****************----------------- Secure Equality Protocol -----------------*****************/
int Node::NchooseK (int n, int k)
{
    if (k == 0)
        return 1;

    return (n * NchooseK(n - 1, k - 1)) / k;
}

void Node::PolyCoeffGen(mpz_t coeff[], djn_pubkey_t * pub, int logL)
{
    mpz_t temp[logL+2];
    int num=2;
    mpz_init_set_ui(coeff[0], 1);

    for (int i = 1; i < logL + 2; i++)
        mpz_init_set_ui(coeff[i], 0);

    mpz_init_set_ui(temp[0], 0);
    for(int i = 1; i < logL+2; i++)
        mpz_init(temp[i]);

    for (int i = 2; i < logL + 2; i++)
    {
        if (i != 0)
        {
            for (int j = 1; j <= num; j++)
            {
                mpz_mul_ui(temp[j], coeff[j-1], i);
            }

            num += 1;

            for (int j = 0; j < num; j++)
            {
                mpz_sub(coeff[j], coeff[j], temp[j]);
                mpz_mod(coeff[j], coeff[j], pub->n);
            }
        }

    }
}

CipherSet Node::QueryAttributes(Query& q)
{
    CipherSet attributes;
    for(int i=0;i < q.size(); ++i) {
        attributes.push_back(&q[i].attribute);
    }

    return attributes;
}

//Implemented NEL-1 protocol from Efficient and Secure Equality Tests
void Node::SecureEqualityProtocol(mpz_t res, mpz_t a, mpz_t b, djn_pubkey_t* pub, djn_prvkey_t* prv)
{
    double timeSpent = 0;
    unsigned int bandwidth = 0;

    int ell = 7, kappa = 112;

    mpz_t n_1;
    mpz_init(n_1);
    mpz_sub_ui(n_1, pub->n, 1);

    //Alice
    //Generate ell+kappa bits random
    mpz_t r, r_enc;
    mpz_inits(r, r_enc, NULL);

    clock_gettime(CLOCK_MONOTONIC, &startT);

    aby_prng(r, ell + kappa);
    djn_encrypt(r_enc, pub, r);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);


    //[x] <- [a - b + r]
    mpz_t x;
    mpz_init(x);

    clock_gettime(CLOCK_MONOTONIC, &startT);

    mpz_powm(x, b, n_1, pub->n_squared);
    djn_hm_add(pub, x, x, a);
    djn_hm_add(pub, x, x, r_enc);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //Alice -> Bob: [x]
    bandwidth += mpz_sizeinbase(x, 2);

    //Bob
    //Decrypt [x]
    mpz_t x_decr;
    mpz_init(x_decr);

    clock_gettime(CLOCK_MONOTONIC, &startT);

    djn_decrypt(x_decr, pub, prv, x);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //Compute first ell bits of x and encrypt them
    mpz_t x_i_enc[ell], temp;
    mpz_init(temp);

    signed long x_Lbits;
    signed long lBits = 1 << ell;
    bool x_i[ell];

    //get ell bits
    x_Lbits = mpz_mod_ui(temp, x_decr, lBits);

    for (int i = 0; i < ell; i++)
    {
        //get bit x_i within ell bits
        clock_gettime(CLOCK_MONOTONIC, &startT);

        x_i[i] = (x_Lbits >> i) % 2;

        clock_gettime(CLOCK_MONOTONIC, &endT);
        timeSpent += getMillies(startT, endT);

        mpz_init(x_i_enc[i]);
        mpz_set_ui(temp, x_i[i]);

        //encrypt x_i
        clock_gettime(CLOCK_MONOTONIC, &startT);

        djn_encrypt_crt(x_i_enc[i], pub, prv, temp);

        clock_gettime(CLOCK_MONOTONIC, &endT);
        timeSpent += getMillies(startT, endT);

        //Bob -> Alice: [x_i]
        bandwidth += mpz_sizeinbase(x_i_enc[i], 2);
    }

    //Alice
    //Compute [r_i \xor x_i]
    //[d] <- [\sum^{ell-1}_{i = 0}{r_i \xor x_i}]

    mpz_t d, p0, p1, one, zero;
    mpz_inits(d, p0, p1, NULL);

    mpz_init_set_ui(one, 1);
    mpz_init_set_ui(zero, 0);

    djn_encrypt(p1, pub, one);
    djn_encrypt(p0, pub, zero);

    mpz_init_set(d, p0);

    unsigned long rL = mpz_mod_ui(temp, r, lBits);
    unsigned long r_i_L[ell];

    //perform xor operation
    clock_gettime(CLOCK_MONOTONIC, &startT);
    for (int i = 0; i < ell; i++)
    {
        r_i_L[i] = (rL >> i) % 2;
        // if r_i is 0, add [x + r] homomorphically
        if (r_i_L[i] == 0)
        {
            djn_hm_add(pub, d, d, x_i_enc[i]);
        }
        // else add [1 - x + r] homomorphically
        else
        {
            mpz_powm(temp, x_i_enc[i], n_1, pub->n_squared);
            djn_hm_add(pub, temp, p1, temp);
            djn_hm_add(pub, d, d, temp);
        }
    }
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //mask d with log_2(ell) + kappa bits random r'
    //[y] <- [d + r']
    int logL = log2(ell) + 1;

    mpz_t r_prime, r_prime_enc, y;
    mpz_inits(r_prime, r_prime_enc, y, NULL);

    clock_gettime(CLOCK_MONOTONIC, &startT);

    aby_prng(r_prime, logL + kappa);

    djn_encrypt(y, pub, r_prime);
    djn_hm_add(pub, y, y, d);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //Alice -> Bob: [y]
    bandwidth += mpz_sizeinbase(y, 2);

    //Bob
    //Decrypt y
    mpz_t y_decr;
    mpz_init(y_decr);

    clock_gettime(CLOCK_MONOTONIC, &startT);

    djn_decrypt(y_decr, pub, prv, y);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //compute th efirst log_2(ell) bits of y
    mpz_t y_i_enc[logL];
    signed long y_Lbits;
    int logLBits = 1 << logL;

    bool y_i[logL];

    //get ell bits
    y_Lbits = mpz_mod_ui(temp, y_decr, logLBits);

    for (int i = 0; i < logL; i++)
    {
        //get bit x_i within ell bits
        clock_gettime(CLOCK_MONOTONIC, &startT);

        y_i[i] = (y_Lbits >> i) % 2;

        clock_gettime(CLOCK_MONOTONIC, &endT);
        timeSpent += getMillies(startT, endT);

        mpz_init(y_i_enc[i]);
        mpz_set_ui(temp, y_i[i]);

        //encrypt x_i
        clock_gettime(CLOCK_MONOTONIC, &startT);

        djn_encrypt_crt(y_i_enc[i], pub, prv, temp);

        clock_gettime(CLOCK_MONOTONIC, &endT);
        timeSpent += getMillies(startT, endT);

        //Bob -> Alice: [y_i]
        bandwidth += mpz_sizeinbase(y_i_enc[i], 2);
    }

    //Alice
    //Compute [r'_i \xor y_i]
    //[d'] <- [\sum^{ell-1}_{i = 0}{r'_i \xor y_i}]
    mpz_t d_prime;
    mpz_init(d_prime);

    mpz_init_set(d_prime, p0);

    unsigned long r_prime_L = mpz_mod_ui(temp, r_prime, logLBits);
    unsigned long r_prime_i_L[logL];

    //perform xor operation
    clock_gettime(CLOCK_MONOTONIC, &startT);
    for (int i = 0; i < logL; i++)
    {
        r_prime_i_L[i] = (r_prime_L >> i) % 2;
        // if r_i is 0, add [y + r] homomorphically
        if (r_prime_i_L[i] == 0)
        {
            djn_hm_add(pub, d_prime, d_prime, y_i_enc[i]);
        }
        // else add [1 - y + r] homomorphically
        else
        {
            mpz_powm(temp, y_i_enc[i], n_1, pub->n_squared);
            djn_hm_add(pub, temp, p1, temp);
            djn_hm_add(pub, d_prime, d_prime, temp);
        }
    }
    djn_hm_add(pub, d_prime, d_prime, p1);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //mask d' with log_2(log_2(ell)) + kappa bits random r''
    //[t] <- [d' + r'']
    int loglogL= log2(logL)+1;

    mpz_t r_pp, r_pp_enc, t;
    mpz_inits(r_pp, r_pp_enc, t, NULL);

    clock_gettime(CLOCK_MONOTONIC, &startT);

    aby_prng(r_pp, loglogL + kappa);

    djn_encrypt(t, pub, r_pp);
    djn_hm_add(pub, t, t, d_prime);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //Alice -> Bob: [t]
    bandwidth += mpz_sizeinbase(t, 2);

    //Bob
    //Decrypt [t]
    mpz_t t_decr;
    mpz_init(t_decr);

    clock_gettime(CLOCK_MONOTONIC, &startT);

    djn_decrypt(t_decr, pub, prv, t);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //Compute t^i for 1 < i < log2L
    mpz_t t_power_i[logL], t_power_i_enc[logL];
    mpz_init_set_ui(t_power_i[0], 1);

    mpz_init(t_power_i_enc[0]);
    mpz_set(t_power_i_enc[0], p1);

    for (int i = 1; i <= logL; i++)
    {
        mpz_inits(t_power_i[i], t_power_i_enc[i], NULL);

        clock_gettime(CLOCK_MONOTONIC, &startT);

        mpz_mul(t_power_i[i], t_power_i[i-1], t_decr);
        mpz_mod(t_power_i[i], t_power_i[i], pub->n);

        djn_encrypt_crt(t_power_i_enc[i], pub, prv, t_power_i[i]);

        clock_gettime(CLOCK_MONOTONIC, &endT);
        timeSpent += getMillies(startT, endT);

        //Bob -> Alice: [t^i]
        bandwidth += mpz_sizeinbase(t_power_i_enc[i], 2);
    }

    //Alice
    //Unmask [t^i]
    //[d'^i] <- [t^i - \sum^{i}_{e=1}{comb(i,e).(d'^{i-e}.R^e)}]
    mpz_t d_prime_r[logL+1], d_prime_power_i[logL+1];
    mpz_t ptemp;

    mpz_inits(d_prime_power_i[0], d_prime_power_i[1], NULL);

    clock_gettime(CLOCK_MONOTONIC, &startT);

    mpz_set(d_prime_power_i[0], p1);
    mpz_set(d_prime_power_i[1], d_prime);
    for (int i = 2; i <= logL; i++)
    {
        mpz_inits(d_prime_r[i-1], d_prime_power_i[i], NULL);
        mpz_powm(d_prime_r[i-1], d_prime_power_i[i-1], r_pp, pub->n_squared);

        mpz_init_set_ui(ptemp, 1);

        for (int j = 0; j < i; j++)
        {
            mpz_mul(ptemp, ptemp, r_pp);
            mpz_mod(ptemp, ptemp, pub->n);
        }

        djn_encrypt(temp, pub, ptemp);

        mpz_powm(temp, temp, n_1, pub->n_squared);
        djn_hm_add(pub, d_prime_power_i[i], t_power_i_enc[i], temp);

        for (int k = 1; k <= i-1; k++)
        {
            mpz_powm_ui(temp, d_prime_r[k], NchooseK(i,k), pub->n_squared);

            mpz_powm(temp, temp, n_1, pub->n_squared);
            djn_hm_add(pub, d_prime_power_i[i], d_prime_power_i[i], temp);
        }

        for (int k = 1; k < i; k++)
        {
            mpz_powm(d_prime_r[k], d_prime_r[k], r_pp, pub->n_squared);
        }
    }
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //Construct log2(ell) degree polynomial
    mpz_t coeff[ell + 2], fact;
    PolyCoeffGen(coeff, pub, logL);

    int f = logL + 1;

    mpz_init(fact);
    mpz_fac_ui(fact, f - 1);
    mpz_invert(fact, fact, pub->n);
    if (logL % 2 == 1)
    {
        mpz_sub(fact, pub->n, fact);
    }

    //Compute the result
    clock_gettime(CLOCK_MONOTONIC, &startT);

    mpz_set(res, p0);
    for (int i = 0; i < logL + 1; i++)
    {
        if (mpz_cmp_ui(coeff[logL - i], 0) != 0)
        {
            mpz_powm(temp, d_prime_power_i[i], coeff[logL-i], pub->n_squared);
            djn_hm_add(pub, res, res, temp);
        }
    }
    mpz_powm(res, res, fact, pub->n_squared);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    this->timeSpent += timeSpent;
    this->bandwidth += bandwidth;
    //printf("One pass of secure equality protocol took %fs\n", timeSpent / 1000);
}

/*****************----------------- Secure Equality Protocol -----------------*****************/

/*****************----------------- Secure Comparison Protocol -----------------*****************/
void Node::SecureComparisonProtocol(mpz_t res, mpz_t a, mpz_t b, djn_pubkey_t* pub, djn_prvkey_t* prv)
{
    double timeSpent = 0;
    unsigned int bandwidth = 0;
    int ell = 7, kappa = 112;

    mpz_t n_1;
    mpz_init(n_1);
    mpz_sub_ui(n_1, pub->n, 1);

    //Alice
    //[z] <= [2^ell + a - b]
    mpz_t z, minus_b, two, two_ell, enc_two_ell;
    mpz_inits(z, minus_b, two, two_ell, enc_two_ell, NULL);

    clock_gettime(CLOCK_MONOTONIC, &startT);

    mpz_set_ui(two, 2);
    mpz_pow_ui(two_ell, two, ell);

    djn_encrypt(enc_two_ell, pub, two_ell);
    mpz_powm(minus_b, b, n_1, pub->n_squared);

    djn_hm_add(pub, z, enc_two_ell, a);
    djn_hm_add(pub, z, z, minus_b);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //[d] <= [z + r]
    //r \in R such that r is kappa + ell bits
    mpz_t r, enc_r, d;
    mpz_inits(r, enc_r, d, NULL);

    clock_gettime(CLOCK_MONOTONIC, &startT);

    aby_prng(r, kappa + ell);
    //mpz_set_ui(r, 10);
    djn_encrypt(enc_r, pub, r);

    djn_hm_add(pub, d, z, enc_r);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //Alice -> Bob: [d]
    bandwidth += mpz_sizeinbase(d, 2);

    //Bob
    //Decrypt [d]
    mpz_t d_decr;
    mpz_init(d_decr);

    clock_gettime(CLOCK_MONOTONIC, &startT);

    djn_decrypt(d_decr, pub, prv, d);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //d1 <= d mod 2^ell
    //d2 <= floor(d / 2^ell)
    mpz_t d1, d2, d1_enc, d2_enc;
    mpz_inits(d1, d2, d1_enc, d2_enc, NULL);

    clock_gettime(CLOCK_MONOTONIC, &startT);

    mpz_mod(d1, d_decr, two_ell);
    mpz_fdiv_q(d2, d_decr, two_ell);

    djn_encrypt_crt(d1_enc, pub, prv, d1);
    djn_encrypt_crt(d2_enc, pub, prv, d2);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //Bob -> Alice: [d1], [d2]
    bandwidth += mpz_sizeinbase(d1_enc, 2);
    bandwidth += mpz_sizeinbase(d2_enc, 2);


    //Bob
    //i = 0,..., ell - 1
    //t_i = d1_i + \sum^{ell-1}_{j = i+1}{2^j * d1_j}
    mpz_t t_i, d1_i, j2, d1_j, j2d1j, j2d1j_sum, d1_remain_i, d1_remain_j, temp;
    mpz_inits(t_i, d1_i, j2, d1_j, j2d1j, j2d1j_sum, d1_remain_i, d1_remain_j, temp, NULL);

    mpz_t enc_t_i[ell];
    mpz_set(d1_remain_i, d1);

    //i = 0,...,ell - 1
    signed long d1_L_bits;
    signed long Lbits = 1 << ell;

    bool d1_i_L, d1_j_L;

    clock_gettime(CLOCK_MONOTONIC, &startT);
    d1_L_bits = mpz_mod_ui(temp, d1, Lbits);
    for(int i = 0; i < ell; i++)
    {
        // \sum_{j = i+1}^{ell-1}{2^j * d1_j}
        for(int j = i+1; j < ell; j++)
        {
            //2^j
            mpz_pow_ui(j2, two, j);

            //d1_j
            d1_j_L = (d1_L_bits >> j) % 2;
            mpz_set_ui(d1_j, d1_j_L);

            //sum 2^j * d1_j
            mpz_mul(j2d1j, j2, d1_j);
            mpz_add(j2d1j_sum, j2d1j_sum, j2d1j);
        }

        //t_i = d1_i + sum 2jd1j
        //d1_i
        d1_i_L = (d1_L_bits >> i) % 2;
        mpz_set_ui(d1_i, d1_i_L);
        mpz_add(t_i, d1_i, j2d1j_sum);

        //Bob -> Alice : [t_i]
        mpz_init(enc_t_i[i]);
        djn_encrypt_crt(enc_t_i[i], pub, prv, t_i);

        bandwidth += mpz_sizeinbase(enc_t_i[i], 2);
    }
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);


    //Alice
    //choose s \in {-1, 1}
    mpz_t  s, enc_v_i, c_i, h_i, v_i, j2rj, j2rj_sum, r_j, r_i, r_remain_i, r_remain_j;
    mpz_inits(s, enc_v_i, c_i, h_i, v_i, j2rj, j2rj_sum, r_j, r_i, r_remain_i, r_remain_j, NULL);

    mpz_t e_i[ell];

    mpz_set(r_remain_i, r);
    mpz_set_si(s, 1);

    //i = 0,...,ell - 1
    signed long r_L_bits;
    bool r_i_L, r_j_L;

    clock_gettime(CLOCK_MONOTONIC, &startT);

    r_L_bits = mpz_mod_ui(temp, r, Lbits);
    for(int i = 0; i < ell; i++)
    {
        //h_i \in_R Z^*_n
        aby_prng(h_i, mpz_sizeinbase(pub->n, 2));
        //mpz_set_ui(h_i, 10);

        mpz_set_ui(j2rj_sum, 0);

        //v_i = s - r_i - \sum_{j = i+1}^{ell-1}(2^j * r_j)
        for(int j = i+1; j < ell; j++)
        {
            //2^j
            mpz_pow_ui(j2, two, j);

            //d1_j
            r_j_L = (r_L_bits >> j) % 2;
            mpz_set_ui(r_j, r_j_L);

            //sum 2^j * d1_j
            mpz_mul(j2rj, j2, r_j);
            mpz_add(j2rj_sum, j2rj_sum, j2rj);
        }

        //v_i = s - r_i - sum 2jrj
        //r_i
        r_i_L = (r_L_bits >> i) % 2;
        mpz_set_ui(r_i, r_i_L);

        //s - r_i
        mpz_sub(v_i, s, r_i);

        //s - ri -sum2jrj
        mpz_sub(v_i, v_i, j2rj_sum);
        mpz_mod(v_i, v_i, pub->n);

        //[c_i] <= [v_i].[t_i]
        djn_encrypt(enc_v_i, pub, v_i);
        djn_hm_add(pub, c_i, enc_v_i, enc_t_i[i]);

        //[e_i] <= [c_i]^{h_i}
        mpz_init(e_i[i]);
        djn_hm_scalarmult(pub, e_i[i], c_i, h_i);

        //Alice -> Bob: [e_i]
        bandwidth += mpz_sizeinbase(e_i[i], 2);
    }
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //Bob
    mpz_t decr_e, lambda_prime, enc_lambda_prime, lambda;
    mpz_inits(decr_e, lambda_prime, enc_lambda_prime, lambda, NULL);

    // if e_i = 0 lambda_prime <= 1
    // else       lambda_prime <= 0
    clock_gettime(CLOCK_MONOTONIC, &startT);
    for(int i = 0; i < ell; i++)
    {
        djn_decrypt(decr_e, pub, prv, e_i[i]);

        if(mpz_cmp_ui(decr_e, 0) == 0)
        {
            mpz_set_ui(lambda_prime, 1);
            break;
        }
        else
        {
            mpz_set_ui(lambda_prime, 0);
        }
    }
    //Bob -> Alice: [lambda_prime]
    djn_encrypt_crt(enc_lambda_prime, pub, prv, lambda_prime);
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    bandwidth += mpz_sizeinbase(enc_lambda_prime, 2);

    //Alice
    //if s = 1  [lambda] <= [lambda_prime]
    //else      [lambda] <= [1][lambda]^{-1}
    clock_gettime(CLOCK_MONOTONIC, &startT);
    if(mpz_cmp_ui(s, 1) == 0)
    {
        mpz_set(lambda, enc_lambda_prime);
    }
    else
    {
        mpz_t minus_lambda, one ,enc_one;
        mpz_inits(minus_lambda, one, enc_one, NULL);

        mpz_powm(minus_lambda, enc_lambda_prime, n_1, pub->n_squared);

        mpz_set_ui(one, 1);
        djn_encrypt(enc_one, pub, one);
        djn_hm_add(pub, lambda, enc_one, minus_lambda);
    }
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //[z_ell] <= [d2].[floor(r/2^ell)]^{-1}.[lambda]^{-1}
    mpz_t r2, r2_enc;
    mpz_inits( r2, r2_enc, NULL);

    clock_gettime(CLOCK_MONOTONIC, &startT);

    //[floor(r/2^ell)]
    mpz_fdiv_q(r2, r, two_ell);

    //[floor(r/2^ell)]
    djn_encrypt(r2_enc, pub, r2);

    //[lambda]
    djn_decrypt(temp, pub, prv, lambda);

    //[r/2^ell + lambda]^-1
    djn_hm_add(pub, res, lambda, r2_enc);

    mpz_powm(res, res, n_1, pub->n_squared);

    djn_hm_add(pub, res, res, d2_enc);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    this->timeSpent += timeSpent;
    this->bandwidth += bandwidth;

    //printf("One pass of secure comparison protocol took %fs\n", timeSpent / 1000);
}
/*****************----------------- Secure Comparison Protocol -----------------*****************/

/*****************----------------- Secure Multiplication Protocol -----------------*****************/
void Node::SecureMultiplicationProtocol(mpz_t res, mpz_t a, mpz_t b, djn_pubkey_t* pub, djn_prvkey_t* prv)
{
    double timeSpent = 0;
    unsigned int bandwidth = 0;

    int ell = 2, kappa = 112;

    //for subtraction operations
    mpz_t n_1;
    mpz_init(n_1);
    mpz_sub_ui(n_1, pub->n, 1);

    //Alice
    //generate randoms r_a and r_b
    mpz_t r_a, r_b, a_prime_enc, b_prime_enc, n_r_a, n_r_b;
    mpz_inits(r_a, r_b, a_prime_enc, b_prime_enc, n_r_a, n_r_b, NULL);

    clock_gettime(CLOCK_MONOTONIC, &startT);
    //r_a
    aby_prng(r_a, kappa + ell);

    //r_b
    aby_prng(r_b, kappa + ell);

    //[a'] = [a - r_a]
    djn_encrypt(n_r_a, pub, r_a);
    mpz_powm(n_r_a, n_r_a, n_1, pub->n_squared);

    djn_hm_add(pub, a_prime_enc, a, n_r_a);

    //[b'] = [b - r_b]
    djn_encrypt(n_r_b, pub, r_b);
    mpz_powm(n_r_b, n_r_b, n_1, pub->n_squared);

    djn_hm_add(pub, b_prime_enc, b, n_r_b);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //Alice -> Bob: [a'] [b']
    bandwidth += mpz_sizeinbase(a_prime_enc, 2);
    bandwidth += mpz_sizeinbase(b_prime_enc, 2);

    //Bob
    //Decrypt [a'] [b']
    mpz_t a_prime, b_prime, ab_prime, ab_prime_enc;
    mpz_inits(a_prime, b_prime, ab_prime, ab_prime_enc, NULL);

    clock_gettime(CLOCK_MONOTONIC, &startT);
    //a' <- [a']
    djn_decrypt(a_prime, pub, prv, a_prime_enc);

    //b' <- [b']
    djn_decrypt(b_prime, pub, prv, b_prime_enc);

    //Multiply a'. b'
    mpz_mul(ab_prime, a_prime, b_prime);
    mpz_mod(ab_prime, ab_prime, pub->n);

    //Bob -> Alice: [a'.b']
    djn_encrypt_crt(ab_prime_enc, pub, prv, ab_prime);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    bandwidth += mpz_sizeinbase(ab_prime_enc, 2);

    //Alice
    //[a'.b'] + [a]^r_b + [b]^r_a + [-r_a.r_b]
    mpz_t a_r_b, b_r_a, r_a_r_b;
    mpz_inits(a_r_b, b_r_a, r_a_r_b, NULL);

    clock_gettime(CLOCK_MONOTONIC, &startT);
    //[a]^r_b
    djn_hm_scalarmult(pub, a_r_b, a, r_b);

    //[b]^r_a
    djn_hm_scalarmult(pub, b_r_a, b, r_a);

    //[-r_a.r_b]
    mpz_mul(r_a_r_b, r_a, r_b);
    mpz_mod(r_a_r_b, r_a_r_b, pub->n);

    djn_encrypt(r_a_r_b, pub, r_a_r_b);
    mpz_powm(r_a_r_b, r_a_r_b, n_1, pub->n_squared);

    //combine all
    djn_hm_add(pub, res, ab_prime_enc, a_r_b);
    djn_hm_add(pub, res, res, b_r_a);
    djn_hm_add(pub, res, res, r_a_r_b);

    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    //printf("One pass of secure multiplication protocol took %fs\n", timeSpent / 1000);
    this->timeSpent += timeSpent;
    this->bandwidth += bandwidth;
}

// Secure Negation Protocol
void Node::SNP(mpz_t res, mpz_t a, djn_pubkey_t* pub, mpz_t n_minus_1)
{
	clock_gettime(CLOCK_MONOTONIC, &startT);
	mpz_t one, enc_1;
    mpz_inits(one, enc_1, NULL);
	mpz_set_ui(one, 1);
	djn_encrypt(enc_1, pub, one);
	mpz_powm(res, a, n_minus_1, pub->n_squared);
	djn_hm_add(pub, res, res, enc_1);
	clock_gettime(CLOCK_MONOTONIC, &endT);

	this->timeSpent += this->getMillies(startT, endT);
}

// Secure Disjunction Protocol
void Node::SDP(mpz_t res, mpz_t a, mpz_t b, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1)
{
	mpz_t a_mul_b, ab, sdp_res;
    mpz_inits(a_mul_b, ab, sdp_res, NULL);

	djn_hm_add(pub, ab, a, b);
	this->SecureMultiplicationProtocol(a_mul_b, a, b, pub, prv);

	mpz_powm(a_mul_b, a_mul_b, n_minus_1, pub->n_squared);
	djn_hm_add(pub, sdp_res, ab, a_mul_b);
    mpz_set(res, sdp_res);


}

// Secure Conjunction Protocol
void Node::SCP(mpz_t res, mpz_t a, mpz_t b, djn_pubkey_t* pub,  djn_prvkey_t* prv)
{
	this->SecureMultiplicationProtocol(res, a, b, pub, prv);
}

void Node::po(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, mpz_t t2_t, mpz_t t2_f, mpz_t t2_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1)
{
    // t
    this->SDP(t, t1_t, t2_t, pub, prv, n_minus_1);
    
    // f
    mpz_t left, right, neg_t2_t, neg_t1_t;
    mpz_inits(left, right, neg_t2_t, neg_t1_t, NULL);
    this->SNP(neg_t2_t, t2_t, pub, n_minus_1);
    this->SCP(left, t1_f, neg_t2_t, pub, prv);

    this->SNP(neg_t1_t, t1_t, pub, n_minus_1);
    this->SCP(right, t2_f, neg_t1_t, pub, prv);

    this->SDP(f, left, right, pub, prv, n_minus_1);

    // u
    this->SCP(u, t1_u, t2_u, pub, prv);
}

void Node::Do(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, mpz_t t2_t, mpz_t t2_f, mpz_t t2_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1)
{
    // t
    mpz_t left, right, neg_t2_f, neg_t1_f, res_t, res_f, res_u;
    mpz_inits(left, right, neg_t2_f, neg_t1_f, res_t, res_f, res_u, NULL);
    this->SNP(neg_t2_f, t2_f, pub, n_minus_1);
    this->SCP(left, t1_t, neg_t2_f, pub, prv);

    this->SNP(neg_t1_f, t1_f, pub, n_minus_1);
    this->SCP(right, t2_t, neg_t1_f, pub, prv);

    this->SDP(res_t, left, right, pub, prv, n_minus_1);
    // f
    this->SDP(res_f, t1_f, t2_f, pub, prv, n_minus_1);

    // u
    this->SCP(res_u, t1_u, t2_u, pub, prv);

    mpz_set(t, res_t);
    mpz_set(f, res_f);
    mpz_set(u, res_u);
}

void Node::fa(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, mpz_t t2_t, mpz_t t2_f, mpz_t t2_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1)
{
    mpz_t t_temp, f_temp;
    mpz_inits(t_temp, f_temp, NULL);

    // t
    this->SCP(t_temp, t1_u, t2_t, pub, prv);
    this->SDP(t, t1_t, t_temp, pub, prv, n_minus_1);

    // f
    this->SCP(f_temp, t1_u, t2_f, pub, prv);
    this->SDP(f, t1_f, f_temp, pub, prv, n_minus_1);

    // u
    this->SCP(u, t1_u, t2_u, pub, prv);
}

void Node::smax(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, mpz_t t2_t, mpz_t t2_f, mpz_t t2_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1)
{
    // t
    this->SDP(t, t1_t, t2_t, pub, prv, n_minus_1);

    // f
    this->SCP(f, t1_f, t2_f, pub, prv);

    // u
    mpz_t left, right, neg_t2_t, neg_t1_t;
    mpz_inits(left, right, neg_t2_t, neg_t1_t, NULL);

    this->SNP(neg_t2_t, t2_t, pub, n_minus_1);
    this->SCP(left, t1_u, neg_t2_t, pub, prv);

    this->SNP(neg_t1_t, t1_t, pub, n_minus_1);
    this->SCP(right, t2_u, neg_t1_t, pub, prv);

    this->SDP(u, left, right, pub, prv, n_minus_1);
}


void Node::smin(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, mpz_t t2_t, mpz_t t2_f, mpz_t t2_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1)
{
    // t
    this->SCP(t, t1_t, t2_t, pub, prv);

    // f 
    this->SDP(f, t1_f, t2_f, pub, prv, n_minus_1);

    // u
    mpz_t left, right, neg_t2_f, neg_t1_f;
    mpz_inits(left, right, neg_t2_f, neg_t1_f, NULL);

    this->SNP(neg_t2_f, t2_f, pub, n_minus_1);
    this->SCP(left, t1_u, neg_t2_f, pub, prv);

    this->SNP(neg_t1_f, t1_f, pub, n_minus_1);
    this->SCP(right, t2_u, neg_t1_f, pub, prv);

    this->SDP(u, left, right, pub, prv, n_minus_1);
}

void Node::wmax(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, mpz_t t2_t, mpz_t t2_f, mpz_t t2_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1)
{
    // t
    mpz_t left, right, neg_t1_u, neg_t2_u;
    mpz_inits(left, right, neg_t1_u, neg_t2_u, NULL);
    this->SNP(neg_t2_u, t2_u, pub, n_minus_1);
    this->SCP(left, t1_t, neg_t2_u, pub, prv);
    this->SNP(neg_t1_u, t1_u, pub, n_minus_1);
    this->SCP(right, t2_t, neg_t1_u, pub, prv);
    this->SDP(t, left, right, pub, prv, n_minus_1);

    // f
    this->SCP(f, t1_f, t2_f, pub, prv);

    // u
    this->SDP(u, t1_u, t2_u, pub, prv, n_minus_1);
}

void Node::wmin(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, mpz_t t2_t, mpz_t t2_f, mpz_t t2_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1)
{
    // t
    this->SCP(t, t1_t, t2_t, pub, prv);
    
    // f 
    mpz_t left, right, neg_t2_u, neg_t1_u;
    mpz_inits(left, right, neg_t2_u, neg_t1_u, NULL);
    this->SNP(neg_t2_u, t2_u, pub, n_minus_1);
    this->SCP(left, t1_f, neg_t2_u, pub, prv);

    this->SNP(neg_t1_u, t1_u, pub, n_minus_1);
    this->SCP(right, t2_f, neg_t1_u, pub, prv);

    this->SDP(f, left, right, pub, prv, n_minus_1);
    // u
    this->SDP(u, t1_u, t2_u, pub, prv, n_minus_1);
}

void Node::Not(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1)
{
    mpz_set(t, t1_f);
    mpz_set(f, t1_t);
    mpz_set(u, t1_u);
}
                                                                        
void Node::wea(mpz_t t, mpz_t f, mpz_t u, mpz_t t1_t, mpz_t t1_f, mpz_t t1_u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1)
{
    mpz_t zero, f_res, zero_enc;
    mpz_inits(zero, f_res, zero_enc, NULL);
    mpz_set_ui(zero, 0);
    djn_encrypt(zero_enc, pub, zero);

    mpz_set(t, t1_t);
    this->SDP(f_res, t1_f, t1_u, pub, prv, n_minus_1);

    mpz_set(f, f_res);
    mpz_set(u, zero_enc);
}

/*****************----------------- Secure Multiplication Protocol -----------------*****************/

void Operation::evaluate(mpz_t t, mpz_t f, mpz_t u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1, Query q)
{
    mpz_t t_res, f_res, u_res, t1_t, t1_f, t1_u, t2_t, t2_f, t2_u;
    mpz_inits(t_res, f_res, u_res, t1_t, t1_f, t1_u, t2_t, t2_f, t2_u, NULL);

    if(this->child2 == NULL) {
        this->child1->evaluate(t1_t, t1_f, t1_u, pub, prv, n_minus_1, q);

        if(this->rule == NOT) {
            this->Not(t_res, f_res, u_res, t1_t, t1_f, t1_u, pub, prv, n_minus_1);
        }
        else if(this->rule == WEA) {
            this->wea(t_res, f_res, u_res, t1_t, t1_f, t1_u, pub, prv, n_minus_1);
        }
        else {
            std::cout << "Trying to perform operation on one child that requires two children." << std::endl;
        }
        mpz_set(t, t_res);
        mpz_set(f, f_res);
        mpz_set(u, u_res);

        this->bandwidth += this->child1->bandwidth;
        this->timeSpent += this->child1->timeSpent;
    }
    else {
        this->child1->evaluate(t1_t, t1_f, t1_u, pub, prv, n_minus_1, q);
        this->child2->evaluate(t2_t, t2_f, t2_u, pub, prv, n_minus_1, q);

        switch(this->rule) {
            case SMAX:
                this->smax(t_res, f_res, u_res, t1_t, t1_f, t1_u, t2_t, t2_f, t2_u, pub, prv, n_minus_1);
                break;
            case SMIN:
                this->smin(t_res, f_res, u_res, t1_t, t1_f, t1_u, t2_t, t2_f, t2_u, pub, prv, n_minus_1);
                break;
            case WMAX:
                this->wmax(t_res, f_res, u_res, t1_t, t1_f, t1_u, t2_t, t2_f, t2_u, pub, prv, n_minus_1);
                break;
            case WMIN:
                this->wmin(t_res, f_res, u_res, t1_t, t1_f, t1_u, t2_t, t2_f, t2_u, pub, prv, n_minus_1);
                break;
            case PO:
                this->po(t_res, f_res, u_res, t1_t, t1_f, t1_u, t2_t, t2_f, t2_u, pub, prv, n_minus_1);
                break;
            case DO:
                this->Do(t_res, f_res, u_res, t1_t, t1_f, t1_u, t2_t, t2_f, t2_u, pub, prv, n_minus_1);
                break;
            default:
                this->fa(t_res, f_res, u_res, t1_t, t1_f, t1_u, t2_t, t2_f, t2_u, pub, prv, n_minus_1);
        }
        mpz_set(t, t_res);
        mpz_set(f, f_res);
        mpz_set(u, u_res);

        this->bandwidth += this->child1->bandwidth;
        this->bandwidth += this->child2->bandwidth;
        this->timeSpent += this->child1->timeSpent;
        this->timeSpent += this->child2->timeSpent;
    }
}

void Leaf::evaluate(mpz_t t, mpz_t f, mpz_t u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1, Query q)
{
    mpz_t zero, enc_0, equal, res;
    mpz_inits(zero, enc_0, equal, res, NULL);
	mpz_set_ui(zero, 0);

    // u
    djn_encrypt(enc_0, pub, zero);
    mpz_set(u, enc_0);

    // f
    this->SecureEqualityProtocol(res, this->value, enc_0, pub, prv);
    mpz_set(f, res);

    // t
    mpz_set(t, this->value);

    /*mpz_t d1, d2, d3;
    mpz_inits(d1, d2, d3, NULL);

    djn_decrypt(d1, pub, prv, t);
    djn_decrypt(d2, pub, prv, f);
    djn_decrypt(d1, pub, prv, u);

    gmp_printf("Leaf: %Zd, %Zd, %Zd\n", d1, d2, d3);
    */
}

void Target::target_evaluate(mpz_t t, mpz_t f, mpz_t u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1, Query q)
{

    mpz_t zero, M, one, two, three, four, zero_enc, one_enc, two_enc, three_enc, four_enc, matching, attribute_match, value_equal, value_not_equal, value_smaller_equal, value_smaller, value_greater, value_match, cond_match, c2, c3, c4, match, NM, included, temp, res_t, res_f, res_u;
    mpz_inits(zero, M, one, two, three, four, zero_enc, one_enc, two_enc, three_enc, four_enc, matching, attribute_match, value_equal, value_not_equal, value_smaller_equal, value_smaller, value_greater, value_match, cond_match, c2, c3, c4, match, NM, included, temp, res_t, res_f, res_u, NULL);
    mpz_set_ui(zero, 0);
    mpz_set_ui(one, 1);
    mpz_set_ui(two, 2);
    mpz_set_ui(three, 3);
    mpz_set_ui(four, 4);
    djn_encrypt(M, pub, zero);
    djn_encrypt(zero_enc, pub, zero);
    djn_encrypt(one_enc, pub, one);
    djn_encrypt(two_enc, pub, two);
    djn_encrypt(three_enc, pub, three);
    djn_encrypt(four_enc, pub, four);

    for (int i = 0; i < q.size(); i++) {
        this->SecureEqualityProtocol(value_equal, q[i].value, this->value, pub, prv);
        this->SecureEqualityProtocol(cond_match, one_enc, this->condition, pub, prv);
        this->SecureMultiplicationProtocol(value_match, value_equal, cond_match, pub, prv);

        mpz_t t1, t2, t3;
        mpz_inits(t1, t2, t3, NULL);

        // c2
        this->SNP(value_not_equal, value_equal, pub, n_minus_1);
        this->SecureEqualityProtocol(cond_match, two_enc, this->condition, pub, prv);
        this->SecureMultiplicationProtocol(c2, value_not_equal, cond_match, pub, prv);

        // c3
        this->SecureComparisonProtocol(value_greater, this->value, q[i].value, pub, prv);
        this->SecureEqualityProtocol(cond_match, three_enc, this->condition, pub, prv);
        this->SecureMultiplicationProtocol(c3, value_greater, cond_match, pub, prv);

        djn_decrypt(t2, pub, prv, cond_match);
        // c4
        this->SNP(value_smaller_equal, value_greater, pub, n_minus_1);
        djn_hm_add(pub, value_smaller, value_smaller_equal, value_equal);
        this->SecureEqualityProtocol(cond_match, four_enc, this->condition, pub, prv);
        this->SecureMultiplicationProtocol(c4, value_smaller, cond_match, pub, prv);

        mpz_t a, b, at, bt, test, test2;
        mpz_inits(a, b, at, bt, test, test2, NULL);

        mpz_set_ui(a, 6);
        mpz_set_ui(b, 10);

        djn_encrypt(at, pub, a);
        djn_encrypt(bt, pub, b);

        this->SecureEqualityProtocol(test, at, bt, pub, prv);
        djn_decrypt(test2, pub, prv, test);
        //gmp_printf("Test: %Zd\n", test2);




        
        djn_decrypt(t1, pub, prv, value_greater);
        djn_decrypt(t3, pub, prv, c3);
        //gmp_printf("c3: %Zd, %Zd, %Zd\n", t1, t2, t3);

        mpz_t d1, d2, d3, d4;
        mpz_inits(d1, d2, d3, d4, NULL);
    

        djn_decrypt(d1, pub, prv, value_match);
        djn_decrypt(d2, pub, prv, c2);
        djn_decrypt(d3, pub, prv, c3);
        djn_decrypt(d4, pub, prv, c4);

        //gmp_printf("Target eval: %Zd, %Zd, %Zd, %Zd\n", d1, d2, d3, d4);

        clock_gettime(CLOCK_MONOTONIC, &startT);
        djn_hm_add(pub, value_match, value_match, c2);
        djn_hm_add(pub, value_match, value_match, c3);
        djn_hm_add(pub, value_match, value_match, c4);
        clock_gettime(CLOCK_MONOTONIC, &endT);
        this->timeSpent += this->getMillies(startT, endT);
        this->SecureEqualityProtocol(attribute_match, this->attribute, q[i].attribute, pub, prv);
        this->SecureMultiplicationProtocol(match, value_match, attribute_match, pub, prv);

        mpz_t a1, a2, a3;
        mpz_inits(a1, a2, a3, NULL);

        djn_decrypt(a1, pub, prv, this->attribute);
        djn_decrypt(a2, pub, prv, q[i].attribute);
        djn_decrypt(a3, pub, prv, attribute_match);

        //gmp_printf("match: %Zd, %Zd, %Zd\n", a1, a2, a3);
        djn_hm_add(pub, M, M, match);
    }

    this->SecureComparisonProtocol(M, M, one_enc, pub, prv);
    this->SNP(NM, M, pub, n_minus_1);

    mpz_powm(included, this->attribute, n_minus_1, pub->n_squared);
    djn_hm_add(pub, included, included, q[0].attribute);
    for(int i = 1; i < q.size(); i++) {
        mpz_powm(temp, this->attribute, n_minus_1, pub->n_squared);
        djn_hm_add(pub, temp, temp, q[i].attribute);
        this->SecureMultiplicationProtocol(included, included, temp, pub, prv);
    }
    this->SecureEqualityProtocol(included, included, zero_enc, pub, prv);

    this->SCP(t, included, M, pub, prv);
    this->SCP(f, included, NM, pub, prv);
    this->SNP(u, included, pub, n_minus_1);

    //mpz_set(t, res_t);
   // mpz_set(f, res_f);
    //mpz_set(u, res_u);
}

void Target::evaluate(mpz_t t, mpz_t f, mpz_t u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1, Query q)
{
    mpz_t res_t, res_f, res_u, eval_t_t, eval_t_f, eval_t_u, eval_p_t, eval_p_f, eval_p_u, eval_t_f_or_u, eval_t_t_and_p_u;
    mpz_inits(res_t, res_f, res_u, eval_t_t, eval_t_f, eval_t_u, eval_p_t, eval_p_f, eval_p_u, eval_t_f_or_u, eval_t_t_and_p_u, NULL);

    this->child1->evaluate(eval_t_t, eval_t_f, eval_t_u, pub, prv, n_minus_1, q);
    this->target_evaluate(eval_p_t, eval_p_f, eval_p_u, pub, prv, n_minus_1, q);
    this->timeSpent += this->child1->timeSpent;
    this->bandwidth += this->child1->bandwidth;

    mpz_t d1, d2, d3;
    mpz_inits(d1, d2, d3, NULL);

    djn_decrypt(d1, pub, prv, eval_p_t);
    djn_decrypt(d2, pub, prv, eval_p_f);
    djn_decrypt(d3, pub, prv, eval_p_u);

    //gmp_printf("%Zd, %Zd, %Zd\n", d1, d2, d3);
    
    this->SDP(eval_t_f_or_u, eval_t_f, eval_t_u, pub, prv, n_minus_1);
    this->SCP(eval_t_t_and_p_u, eval_t_t, eval_p_u, pub, prv);

    this->SCP(res_t, eval_t_t, eval_p_t, pub, prv);
    this->SCP(res_f, eval_t_t, eval_p_f, pub, prv);
    this->SDP(res_u, eval_t_f_or_u, eval_t_t_and_p_u, pub, prv, n_minus_1);

    mpz_set(t, res_t);
    mpz_set(f, res_f);
    mpz_set(u, res_u);
}

void DummyTarget::evaluate(mpz_t t, mpz_t f, mpz_t u, djn_pubkey_t* pub, djn_prvkey_t* prv, mpz_t n_minus_1, Query q)
{
    mpz_set(t, this->t);
    mpz_set(f, this->f);
    mpz_set(u, this->u);
}
