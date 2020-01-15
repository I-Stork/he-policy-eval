//
//  main.cpp
//  mina_he
//
//  Created by gtillem on 09/11/2018.
//  Copyright © 2018 gtillem. All rights reserved.
//

#include <iostream>
#include "gmp.h"
#include "djn.h"
#include "utils.h"
#include <cmath>
#include "SEQ.h"

using namespace std;

djn_pubkey_t* pub;
djn_prvkey_t* prv;


/**
 * Return time difference in milliseconds
 */
struct timespec startT, endT;

static double getMillies(timespec timestart, timespec timeend)
{
    long time1 = (timestart.tv_sec * 1000000) + (timestart.tv_nsec / 1000);
    long time2 = (timeend.tv_sec * 1000000) + (timeend.tv_nsec / 1000);
    
    return (double) (time2 - time1) / 1000;
}


/*****************----------------- Secure Equality Protocol -----------------*****************/
int NchooseK (int n, int k)
{
    if (k == 0)
        return 1;
    
    return (n * NchooseK(n - 1, k - 1)) / k;
}

void PolyCoeffGen(mpz_t coeff[], djn_pubkey_t * pub, int logL)
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

//Implemented NEL-1 protocol from Efficient and Secure Equality Tests
double SecureEqualityProtocol(mpz_t res, mpz_t a, mpz_t b, unsigned int & bandwidth)
{
    double timeSpent = 0;
    bandwidth = 0;
    int ell = 2, kappa = 112;
    
    mpz_t n_1;
    mpz_init(n_1);
    mpz_sub_ui(n_1, pub->n, 1);
    
    //Alice
    //Generate ell+kappa bits random
    mpz_t r, r_enc;
    mpz_inits(r, r_enc, NULL);
    
    clock_gettime(CLOCK_MONOTONIC, &startT);
    
    aby_prng(r, ell + kappa);
    gmp_printf("Random r: %Zd\n", r);
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
    
    return timeSpent;
}

/*****************----------------- Secure Equality Protocol -----------------*****************/

/*****************----------------- Secure Comparison Protocol -----------------*****************/
double SecureComparisonProtocol(mpz_t res, mpz_t a, mpz_t b, unsigned int & bandwidth)
{
    double timeSpent = 0;
    
    bandwidth = 0;
    int ell = 2, kappa = 112;
    
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
    
    return timeSpent;
}
/*****************----------------- Secure Comparison Protocol -----------------*****************/

/*****************----------------- Secure Multiplication Protocol -----------------*****************/
double SecureMultiplicationProtocol(mpz_t res, mpz_t a, mpz_t b, unsigned int & bandwidth)
{
    double timeSpent = 0;
    bandwidth = 0;
    
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
    
    return timeSpent;
}
/*****************----------------- Secure Multiplication Protocol -----------------*****************/


////////////////////////////////////////////////////////////////////////////////////////////////////////
//parameters
mpz_t enc_0, enc_1, enc_3; //encryptions of 0, 1, and 3
mpz_t n_minus_1;  // for subtraction

/*****************----------------- Policy Functions -----------------*****************/
//Complement
double Complement(mpz_t res, mpz_t p, unsigned int & bandwidth)
{
    double timeSpent = 0;
    unsigned int local_bandwidth = 0;
    bandwidth = 0;
    
    //[p_comp] = [3] - [p]
    mpz_t minus_p;
    mpz_init(minus_p);
    
    clock_gettime(CLOCK_MONOTONIC, &startT);
    //-[p]
    mpz_powm(minus_p, p, n_minus_1, pub->n_squared);
    //[3] - [p]
    djn_hm_add(pub, res, enc_3, minus_p);
    
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);

    bandwidth = local_bandwidth;
    
    return timeSpent;
}

//Complement Alternative
double Complement_Alt(mpz_t res, mpz_t p, unsigned int & bandwidth)
{
    double timeSpent = 0;
    unsigned int local_bandwidth = 0;
    bandwidth = 0;
    
    //Alternative formulation - to prevent 2 in negation-
    //[p_comp] = [p ?= 1] x [p] + ([1] - [p ?= 1]) x ([3] - [p])
    mpz_t p_eq_1, minus_p_eq_1, t_minus_p, res1, res2;
    mpz_inits(p_eq_1, minus_p_eq_1, t_minus_p, res1, res2, NULL);
    
    clock_gettime(CLOCK_MONOTONIC, &startT);
    //[p ?= 1]
    timeSpent += SecureEqualityProtocol(p_eq_1, p, enc_1, local_bandwidth);
    bandwidth += local_bandwidth;
    //[p ?= 1] x [p]
    timeSpent += SecureMultiplicationProtocol(res1, p_eq_1, p, local_bandwidth);
    bandwidth += local_bandwidth;
    
    // [1] - [p ?= 1]
    mpz_powm(minus_p_eq_1, p_eq_1, n_minus_1, pub->n_squared);
    djn_hm_add(pub, minus_p_eq_1, minus_p_eq_1, enc_1);
    
    //([3] - [p])
    mpz_powm(t_minus_p, p, n_minus_1, pub->n_squared);
    djn_hm_add(pub, t_minus_p, t_minus_p, enc_3);
    
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    //([1] - [p ?= 1]) x ([3] - [p])
    timeSpent += SecureMultiplicationProtocol(res2, t_minus_p, minus_p_eq_1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p ?= 1] x [p] + ([1] - [p ?= 1]) x ([3] - [p])
    clock_gettime(CLOCK_MONOTONIC, &startT);
    djn_hm_add(pub, res, res1, res2);
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    return timeSpent;
}

//Opt
double Opt(mpz_t res, mpz_t p, unsigned int & bandwidth)
{
    double timeSpent = 0;
    unsigned int local_bandwidth = 0;
    bandwidth = 0;
    
    //[p_opt] = ([1] - [p ?= 1]) x [p]
    //[p ?= 1]
    mpz_t p_eq_1;
    mpz_init(p_eq_1);
    
    timeSpent += SecureEqualityProtocol(p_eq_1, enc_1, p, local_bandwidth);
    bandwidth += local_bandwidth;
    
    clock_gettime(CLOCK_MONOTONIC, &startT);
    // - [p ?= 1]
    mpz_powm(p_eq_1, p_eq_1, n_minus_1, pub->n_squared);
    //[1] - [p ?= 1]
    djn_hm_add(pub, p_eq_1, enc_1, p_eq_1);
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    //([1] - [p ?= 1]) x [p]
    timeSpent += SecureMultiplicationProtocol(res, p_eq_1, p, local_bandwidth);
    bandwidth += local_bandwidth;
    
    return timeSpent;
}

//E1
double E1(mpz_t res, mpz_t p, unsigned int & bandwidth)
{
    double timeSpent = 0;
    unsigned int local_bandwidth = 0;
    bandwidth = 0;
    
    //[p_E1] = [p ?= 3] + [p ?= 1] x 3
    mpz_t p_eq_1, p_eq_3;
    mpz_inits(p_eq_1, p_eq_3, NULL);
    
    //[p ?= 1]
    timeSpent += SecureEqualityProtocol(p_eq_1, enc_1, p, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p ?= 3]
    timeSpent += SecureEqualityProtocol(p_eq_3, enc_3, p, local_bandwidth);
    bandwidth += local_bandwidth;
    
    clock_gettime(CLOCK_MONOTONIC, &startT);
    //[p ?= 1] x 3
    mpz_powm_ui(p_eq_1, p_eq_1, 3, pub->n_squared);
    
    //[p ?= 3] + [p ?= 1] x 3
    djn_hm_add(pub, res, p_eq_1, p_eq_3);
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    return timeSpent;
}

//Maximum
double Maximum(mpz_t res, mpz_t p1, mpz_t p2, unsigned int & bandwidth)
{
    double timeSpent = 0;
    unsigned int local_bandwidth = 0;
    bandwidth = 0;
    
    //[p1 Max p2] = [p1 ?> p2] x [p1] + ([1] - [p1 ?> p2]) x [p2]
    //[p1 ?> p2]
    mpz_t p1_cmp_p2, minus_p1_cmp_p2, res1, res2;
    mpz_inits(p1_cmp_p2, minus_p1_cmp_p2, res1, res2, NULL);
    
    timeSpent += SecureComparisonProtocol(p1_cmp_p2, p1, p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    clock_gettime(CLOCK_MONOTONIC, &startT);
    // - [p1 ?> p2]
    mpz_powm(minus_p1_cmp_p2, p1_cmp_p2, n_minus_1, pub->n_squared);
    
    //[1] - [p1 ?> p2]
    djn_hm_add(pub, minus_p1_cmp_p2, enc_1, minus_p1_cmp_p2);
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    //[p1 ?> p2] x [p1]
    timeSpent += SecureMultiplicationProtocol(res1, p1_cmp_p2, p1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //([1] - [p1 ?> p2]) x [p2]
    timeSpent += SecureMultiplicationProtocol(res2, minus_p1_cmp_p2, p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p1 ?> p2] x [p1] + ([1] - [p1 ?> p2]) x [p2]
    clock_gettime(CLOCK_MONOTONIC, &startT);
    djn_hm_add(pub, res, res1, res2);
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    return timeSpent;
}

//Minimum
double Minimum(mpz_t res, mpz_t p1, mpz_t p2, unsigned int & bandwidth)
{
    double timeSpent = 0;
    unsigned int local_bandwidth = 0;
    bandwidth = 0;
    
    //[p1 Min p2] = ([1] - [p1 ?> p2]) x [p1] + [p1 ?> p2] x [p2]
    //[p1 ?> p2]
    mpz_t p1_cmp_p2, minus_p1_cmp_p2, res1, res2;
    mpz_inits(p1_cmp_p2, minus_p1_cmp_p2, res1, res2, NULL);
    
    timeSpent += SecureComparisonProtocol(p1_cmp_p2, p1, p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    clock_gettime(CLOCK_MONOTONIC, &startT);
    // - [p1 ?> p2]
    mpz_powm(minus_p1_cmp_p2, p1_cmp_p2, n_minus_1, pub->n_squared);
    
    //[1] - [p1 ?> p2]
    djn_hm_add(pub, minus_p1_cmp_p2, enc_1, minus_p1_cmp_p2);
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    //([1] - [p1 ?> p2]) x [p1]
    timeSpent += SecureMultiplicationProtocol(res1, minus_p1_cmp_p2, p1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p1 ?> p2] x [p2]
    timeSpent += SecureMultiplicationProtocol(res2, p1_cmp_p2, p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //([1] - [p1 ?> p2]) x [p1] + [p1 ?> p2] x [p2]
    clock_gettime(CLOCK_MONOTONIC, &startT);
    djn_hm_add(pub, res, res1, res2);
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    return timeSpent;
}

//Weak Maximum
double WeakMaximum(mpz_t res, mpz_t p1, mpz_t p2, unsigned int & bandwidth)
{
    double timeSpent = 0;
    unsigned int local_bandwidth = 0;
    bandwidth = 0;
    
    //[p1 w_Max p2] = [p1 ?= 1] XOR [p2 ?= 1] + (1 - [p1 ?= 1] XOR [p2 ?= 1]) x [p1 MAX p2]
    
    //[p1 ?= 1] XOR [p2 ?= 1] = [p1 ?= 1] + [p2 ?= 1] - 2[p1 ?= 1] x [p2 ?= 1]
    mpz_t p1_eq_1, p2_eq_1, p1_mult_p2, p1_xor_p2, minus_p1_xor_p2, p1_min_p2, res1;
    mpz_inits(p1_eq_1, p2_eq_1, p1_mult_p2, p1_xor_p2, minus_p1_xor_p2, p1_min_p2, res1, NULL);
    
    //[p1 ?= 1]
    timeSpent += SecureEqualityProtocol(p1_eq_1, p1, enc_1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p2 ?= 1]
    timeSpent += SecureEqualityProtocol(p2_eq_1, p2, enc_1, local_bandwidth);
    bandwidth += local_bandwidth;  
    
    //[p1 ?= 1] x [p2 ?= 1]
    timeSpent += SecureMultiplicationProtocol(p1_mult_p2, p1_eq_1, p2_eq_1, local_bandwidth);
    bandwidth += local_bandwidth;

    clock_gettime(CLOCK_MONOTONIC, &startT);
    // - 2[p1 ?= 1] x [p2 ?= 1]
    mpz_powm(p1_mult_p2, p1_mult_p2, n_minus_1, pub->n_squared);
    mpz_powm_ui(p1_mult_p2, p1_mult_p2, 2, pub->n_squared);
    
    
    //[p1 ?= 1] + [p2 ?= 1] - 2[p1 ?= 1] x [p2 ?= 1]
    djn_hm_add(pub, p1_xor_p2, p1_eq_1, p2_eq_1);
    djn_hm_add(pub, p1_xor_p2, p1_xor_p2, p1_mult_p2);
    
    //(1 - [p1 ?= 1] XOR [p2 ?= 1])  
    mpz_powm(minus_p1_xor_p2, p1_xor_p2, n_minus_1, pub->n_squared);
    djn_hm_add(pub, minus_p1_xor_p2, enc_1, minus_p1_xor_p2);
    
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    //[p1 MAX p2]
    timeSpent += Maximum(p1_min_p2, p1, p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //(1 - [p1 ?= 1] XOR [p2 ?= 1]) x [p1 MAX p2]
    timeSpent += SecureMultiplicationProtocol(res1, minus_p1_xor_p2, p1_min_p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p1 w_Max p2] = [p1 ?= 1] XOR [p2 ?= 1] + (1 - [p1 ?= 1] XOR [p2 ?= 1]) x [p1 MAX p2]
	clock_gettime(CLOCK_MONOTONIC, &startT);
	
    djn_hm_add(pub, res, p1_xor_p2, res1);
    
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    return timeSpent;
}

//Weak Minimum
double WeakMinimum(mpz_t res, mpz_t p1, mpz_t p2, unsigned int & bandwidth)
{
   double timeSpent = 0;
    unsigned int local_bandwidth = 0;
    bandwidth = 0;
    
    //[p1 w_Min p2] = [p1 ?= 1] XOR [p2 ?= 1] + (1 - [p1 ?= 1] XOR [p2 ?= 1]) x [p1 MIN p2]
    
    //[p1 ?= 1] XOR [p2 ?= 1] = [p1 ?= 1] + [p2 ?= 1] - 2[p1 ?= 1] x [p2 ?= 1]
    mpz_t p1_eq_1, p2_eq_1, p1_mult_p2, p1_xor_p2, minus_p1_xor_p2, p1_min_p2, res1;
    mpz_inits(p1_eq_1, p2_eq_1, p1_mult_p2, p1_xor_p2, minus_p1_xor_p2, p1_min_p2, res1, NULL);
    
    //[p1 ?= 1]
    timeSpent += SecureEqualityProtocol(p1_eq_1, p1, enc_1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p2 ?= 1]
    timeSpent += SecureEqualityProtocol(p2_eq_1, p2, enc_1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    
    //[p1 ?= 1] x [p2 ?= 1]
    timeSpent += SecureMultiplicationProtocol(p1_mult_p2, p1_eq_1, p2_eq_1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    clock_gettime(CLOCK_MONOTONIC, &startT);
    // - 2[p1 ?= 1] x [p2 ?= 1]
    mpz_powm(p1_mult_p2, p1_mult_p2, n_minus_1, pub->n_squared);
    mpz_powm_ui(p1_mult_p2, p1_mult_p2, 2, pub->n_squared);
    
    //[p1 ?= 1] + [p2 ?= 1] - 2[p1 ?= 1] x [p2 ?= 1]
    djn_hm_add(pub, p1_xor_p2, p1_eq_1, p2_eq_1);
    djn_hm_add(pub, p1_xor_p2, p1_xor_p2, p1_mult_p2);
    
    //(1 - [p1 ?= 1] XOR [p2 ?= 1])  
    mpz_powm(minus_p1_xor_p2, p1_xor_p2, n_minus_1, pub->n_squared);
    djn_hm_add(pub, minus_p1_xor_p2, enc_1, minus_p1_xor_p2);
    
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    //[p1 MIN p2]
    timeSpent += Minimum(p1_min_p2, p1, p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //(1 - [p1 ?= 1] XOR [p2 ?= 1]) x [p1 MIN p2]
    timeSpent += SecureMultiplicationProtocol(res1, minus_p1_xor_p2, p1_min_p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p1 w_Min p2] = [p1 ?= 1] XOR [p2 ?= 1] + (1 - [p1 ?= 1] XOR [p2 ?= 1]) x [p1 MIN p2]
	clock_gettime(CLOCK_MONOTONIC, &startT);
	
    djn_hm_add(pub, res, p1_xor_p2, res1);
    
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    return timeSpent;
}

//Permit Override
double PermitOverride(mpz_t res, mpz_t p1, mpz_t p2, unsigned int & bandwidth)
{
    double timeSpent = 0;
    unsigned int local_bandwidth = 0;
    bandwidth = 0;
    
    //[p1 PO p2] = ([p1] Max [opt_p2]) Min ([opt_p1] Max [p2])
    
    mpz_t opt_p1, opt_p2, p1_Max_o_p2, o_p1_Max_p2;
    mpz_inits(opt_p1, opt_p2, p1_Max_o_p2, o_p1_Max_p2, NULL);
    
    //[opt_p1], [opt_p2]
    timeSpent += Opt(opt_p1, p1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    timeSpent += Opt(opt_p2, p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //([p1] Max [opt_p2])
    timeSpent += Maximum(p1_Max_o_p2, p1, opt_p2, local_bandwidth);
    bandwidth += local_bandwidth;
    //([opt_p1] Max [p2])
    timeSpent += Maximum(o_p1_Max_p2, opt_p1, p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //([p1] Max [opt_p2]) Min ([opt_p1] Max [p2])
    timeSpent += Minimum(res, p1_Max_o_p2, o_p1_Max_p2, local_bandwidth);
    bandwidth += local_bandwidth;
    return timeSpent;
}

//Permit Override - Alternative
double PermitOverride_Alt(mpz_t res, mpz_t p1, mpz_t p2, unsigned int & bandwidth)
{
    double timeSpent = 0;
    unsigned int local_bandwidth = 0;
    bandwidth = 0;
    
    //[p1 PO p2] = ([p1 ?= 3] x [p2 ?= 3]) x [3] + ([p1 ?= 3] XOR [p2 ?= 3])x [3] + ([p1 ?= 1] x [p2 ?= 1]) x [1] + [0]
    
    mpz_t p1_eq_3, p2_eq_3, p1_eq_1, p2_eq_1, p1e3_p2e3, pe1_p2e1, p1e3_p2e3_mult, p13_and_p23;
    mpz_inits(p1_eq_3, p2_eq_3, p1_eq_1, p2_eq_1, p1e3_p2e3, pe1_p2e1, p1e3_p2e3_mult, p13_and_p23, NULL);
    
    //[p1 ?= 3]
    timeSpent += SecureEqualityProtocol(p1_eq_3, p1, enc_3, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p2 ?= 3]
    timeSpent += SecureEqualityProtocol(p2_eq_3, p2, enc_3, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //([p1 ?= 3] x [p2 ?= 3])
    timeSpent += SecureMultiplicationProtocol(p13_and_p23, p1_eq_3, p2_eq_3, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //([p1 ?= 3] XOR [p2 ?= 3]) = [p1 ?= 3] + [p2 ?= 3] - 2 . [p1 ?= 3] x [p2 ?= 3]
    //[p1 ?= 3] x [p2 ?= 3]
    timeSpent += SecureMultiplicationProtocol(p1e3_p2e3_mult, p1_eq_3, p2_eq_3, local_bandwidth);
    bandwidth += local_bandwidth;
    
    clock_gettime(CLOCK_MONOTONIC, &startT);
    //- 2 . [p1 ?= 3] x [p2 ?= 3]
    mpz_powm_ui(p1e3_p2e3_mult, p1e3_p2e3_mult, 2, pub->n_squared);
    mpz_powm(p1e3_p2e3_mult, p1e3_p2e3_mult, n_minus_1, pub->n_squared);
    
    //[p1 ?= 3] + [p2 ?= 3]
    djn_hm_add(pub, p1e3_p2e3, p1_eq_3, p2_eq_3);
    
    //[p1 ?= 3] + [p2 ?= 3] - 2 . [p1 ?= 3] x [p2 ?= 3]
    djn_hm_add(pub, p1e3_p2e3, p1e3_p2e3, p1e3_p2e3_mult);
    
    //([p1 ?= 3] x [p2 ?= 3])  + ([p1 ?= 3] XOR [p2 ?= 3])
    djn_hm_add(pub, p1e3_p2e3, p1e3_p2e3, p13_and_p23);
    
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    
    //([p1 ?= 3] x [p2 ?= 3]) x [3] + ([p1 ?= 3] XOR [p2 ?= 3])x [3]
    timeSpent += SecureMultiplicationProtocol(p1e3_p2e3, p1e3_p2e3, enc_3, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p1 ?= 1]
    timeSpent += SecureEqualityProtocol(p1_eq_1, p1, enc_1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p2 ?= 1]
    timeSpent += SecureEqualityProtocol(p2_eq_1, p2, enc_1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //([p1 ?= 1] x [p2 ?= 1])
    timeSpent += SecureMultiplicationProtocol(pe1_p2e1, p1_eq_1, p2_eq_1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //([p1 ?= 3] + [p2 ?= 3])x [3] + ([p1 ?= 1] x [p2 ?= 1]) x [1] + [0]
    clock_gettime(CLOCK_MONOTONIC, &startT);
    djn_hm_add(pub, res, p1e3_p2e3, pe1_p2e1);
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    return timeSpent;
}

//Deny Override
double DenyOverride(mpz_t res, mpz_t p1, mpz_t p2, unsigned int & bandwidth)
{
    double timeSpent = 0;
    unsigned int local_bandwidth = 0;
    bandwidth = 0;
    
    //[p1 DO p2] = comp([comp_p1] PO [comp_p2])
    
    mpz_t comp_p1, comp_p2, c_p1_PO_c_p2;
    mpz_inits(comp_p1, comp_p2, c_p1_PO_c_p2, NULL);
    
    //[comp_p1], [comp_p2]
    timeSpent += Complement_Alt(comp_p1, p1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    timeSpent += Complement_Alt(comp_p2, p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //([comp_p1] PO [comp_p2])
    timeSpent += PermitOverride(c_p1_PO_c_p2, comp_p1, comp_p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //comp([comp_p1] PO [comp_p2])
    timeSpent += Complement_Alt(res, c_p1_PO_c_p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    return timeSpent;
}

//Deny Override - Alternative
double DenyOverride_Alt(mpz_t res, mpz_t p1, mpz_t p2, unsigned int & bandwidth)
{
    double timeSpent = 0;
    unsigned int local_bandwidth = 0;
    bandwidth = 0;
    
    //[p1 DO p2] = [3] x ([p1 ?= 3] x [p2 ?= 3] + [p1 ?= 3] x [p2 ?= 1] + [p1 ?= 1] x [p2 ?= 3])
    //             + [p1 ?= 1] x [p2 ?= 1] x [1]
    
    mpz_t p1_eq_1, p1_eq_3, p2_eq_1, p2_eq_3, p1_p2_33, p1_p2_31, p1_p2_13, p1_p2_11, mult;
    mpz_inits(p1_eq_1, p1_eq_3, p2_eq_1, p2_eq_3, p1_p2_33, p1_p2_31, p1_p2_13, p1_p2_11, mult, NULL);
    
    //[p1 ?= 1]
    timeSpent += SecureEqualityProtocol(p1_eq_1, p1, enc_1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p1 ?= 3]
    timeSpent += SecureEqualityProtocol(p1_eq_3, p1, enc_3, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p2 ?= 1]
    timeSpent += SecureEqualityProtocol(p2_eq_1, p2, enc_1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p2 ?= 3]
    timeSpent += SecureEqualityProtocol(p2_eq_3, p2, enc_3, local_bandwidth);
    bandwidth += local_bandwidth;
    
    // [p1 ?= 3] x [p2 ?= 3]
    timeSpent += SecureMultiplicationProtocol(p1_p2_33, p1_eq_3, p2_eq_3, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p1 ?= 3] x [p2 ?= 1]
    timeSpent += SecureMultiplicationProtocol(p1_p2_31, p1_eq_3, p2_eq_1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p1 ?= 1] x [p2 ?= 3]
    timeSpent += SecureMultiplicationProtocol(p1_p2_13, p1_eq_1, p2_eq_3, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p1 ?= 1] x [p2 ?= 1]
    timeSpent += SecureMultiplicationProtocol(p1_p2_11, p1_eq_1, p2_eq_1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    // ([p1 ?= 3] x [p2 ?= 3] + [p1 ?= 3] x [p2 ?= 1] + [p1 ?= 1] x [p2 ?= 3])
    clock_gettime(CLOCK_MONOTONIC, &startT);
    djn_hm_add(pub, mult, p1_p2_33, p1_p2_31);
    djn_hm_add(pub, mult, mult, p1_p2_13);
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    // [3] x ([p1 ?= 3] x [p2 ?= 3] + [p1 ?= 3] x [p2 ?= 1] + [p1 ?= 1] x [p2 ?= 3])
    timeSpent += SecureMultiplicationProtocol(mult, mult, enc_3, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //summation
    clock_gettime(CLOCK_MONOTONIC, &startT);
    djn_hm_add(pub, res, mult, p1_p2_11);
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    return timeSpent;
}

//First Applicable
double FirstApplicable(mpz_t res, mpz_t p1, mpz_t p2, unsigned int & bandwidth)
{
    double timeSpent = 0;
    unsigned int local_bandwidth = 0;
    bandwidth = 0;
    
    //[p1 FA p2] = p1 PO (p1 DO p2)
    
    mpz_t p1_DO_p2;
    mpz_init(p1_DO_p2);
    
    //(p1 DO p2)
    timeSpent += DenyOverride(p1_DO_p2, p1, p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //p1 PO (p1 DO p2)
    timeSpent += PermitOverride(res, p1, p1_DO_p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    return timeSpent;
}

//First Applicable - Alternative
double FirstApplicable_Alt(mpz_t res, mpz_t p1, mpz_t p2, unsigned int & bandwidth)
{
    double timeSpent = 0;
    unsigned int local_bandwidth = 0;
    bandwidth = 0;
    
    //[p1 FA p2] = ([1] - [p1 ?= 1]) x [p1] + [p1 ?= 1] x [p2]
    mpz_t p1_eq_1, minus_p1_eq_1, res1, res2;
    mpz_inits(p1_eq_1, minus_p1_eq_1, res1, res2, NULL);
    
    //[p1 ?= 1]
    timeSpent += SecureEqualityProtocol(p1_eq_1, p1, enc_1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //([1] - [p1 ?= 1])
    clock_gettime(CLOCK_MONOTONIC, &startT);
    mpz_powm(minus_p1_eq_1, p1_eq_1, n_minus_1, pub->n_squared);
    djn_hm_add(pub, minus_p1_eq_1, minus_p1_eq_1, enc_1);
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    //([1] - [p1 ?= 1]) x [p1]
    timeSpent += SecureMultiplicationProtocol(res1, minus_p1_eq_1, p1, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //[p1 ?= 1] x [p2]
    timeSpent += SecureMultiplicationProtocol(res2, p1_eq_1, p2, local_bandwidth);
    bandwidth += local_bandwidth;
    
    //([1] - [p1 ?= 1]) x [p1] + [p1 ?= 1] x [p2]
    clock_gettime(CLOCK_MONOTONIC, &startT);
    djn_hm_add(pub, res, res1, res2);
    clock_gettime(CLOCK_MONOTONIC, &endT);
    timeSpent += getMillies(startT, endT);
    
    return timeSpent;
}

/*****************----------------- Policy Functions -----------------*****************/

void ScalabilityTest()
{
	//possible inputs -> 0, 1, 3
	//possible operations -> INV: 1, OPT: 2, E(.): 3, MIN: 4, MAX: 5, WMIN: 6, WMAX: 7, PO: 8, DO: 9, FA: 10
	 
	int NUM_INPUTS = 2;
	int NUM_TESTS = 20; 
	
	srand(time(NULL));
    mpz_t enc_d1, enc_d2, d1, d2, res, output;
    int op, aux_op;
    
    mpz_inits(enc_d1, enc_d2, res, output, NULL);
    
	std::string input2;
	
	//Generate inputs from 2 to 20 randomly
	while(NUM_INPUTS <= 50)
	{
		double timeSpent = 0;
        unsigned int bandwidth = 0, local_bandwidth = 0;
		int ctr = 0;
		std::cout << "\n\nNumber of Inputs: " << NUM_INPUTS << std::endl;
		
		//Run 20 experiments
		for(int i = 0; i < NUM_TESTS; i++)
		{
			//pick the first input randomly
			int d = rand() % 4;
            if(d == 2)
                d = 1;
            mpz_init_set_ui(d1, d);
            djn_encrypt(enc_d1, pub, d1);
                
            //gmp_printf("%Zd ", d1);
                      
            for(int j = 0; j < NUM_INPUTS - 1; j++)
            {
				ctr++;
				d = rand() % 4;
				if(d == 2)
					d = 1;
			 	mpz_init_set_ui(d2, d);
			 	djn_encrypt(enc_d2, pub, d2);
				
				//pick the operation randomly
				op = rand() % 10 + 1;
				if(op == 1 || op == 2 || op == 3)
				{
					aux_op = op; 
					op = rand() % 7 + 4;
				}
				else
					aux_op = 0;
					
				if(aux_op > 0)
				{	
					switch (aux_op)
					{
						case 1:
							timeSpent += Complement_Alt(enc_d2, enc_d2, local_bandwidth);
							bandwidth += (local_bandwidth / 8);
							input2 = std::string("INV ") + std::to_string(d);
							break;
						case 2:
							timeSpent += Opt(enc_d2, enc_d2, local_bandwidth);
							bandwidth += (local_bandwidth / 8);
							input2 = std::string("OPT ") + std::to_string(d);
							break;
						case 3:
							timeSpent += E1(enc_d2, enc_d2, local_bandwidth);
							bandwidth += (local_bandwidth / 8);
							input2 = std::string("E() ") + std::to_string(d);
							break;
						default:
							break;
					}
									
				}	
				else
					input2 = std::to_string(d);
				
				switch (op)
				{
					case 4:
						timeSpent += Minimum(enc_d1, enc_d1, enc_d2, local_bandwidth);
						bandwidth += (local_bandwidth / 8);
						//std::cout << "MIN " << input2 << " "; 
						break;
					case 5:
						timeSpent += Maximum(enc_d1, enc_d1, enc_d2, local_bandwidth);
						bandwidth += (local_bandwidth / 8);
						//std::cout << "MAX " << input2 << " "; 
						break;
					case 6:
						timeSpent += WeakMinimum(enc_d1, enc_d1, enc_d2, local_bandwidth);
						bandwidth += (local_bandwidth / 8);
						//std::cout << "WMIN " << input2 << " "; 
						break;
					case 7:
						timeSpent += WeakMaximum(enc_d1, enc_d1, enc_d2, local_bandwidth);
						bandwidth += (local_bandwidth / 8);
						//std::cout << "WMAX " << input2 << " "; 
						break;
					case 8:
						timeSpent += PermitOverride_Alt(enc_d1, enc_d1, enc_d2, local_bandwidth);
						bandwidth += (local_bandwidth / 8);
						//std::cout << "PO " << input2 << " "; 
						break;
					case 9:
						timeSpent += DenyOverride_Alt(enc_d1, enc_d1, enc_d2, local_bandwidth);
						bandwidth += (local_bandwidth / 8);
						//std::cout << "DO " << input2 << " "; 
						break;
					case 10:
						timeSpent += FirstApplicable_Alt(enc_d1, enc_d1, enc_d2, local_bandwidth);
						bandwidth += (local_bandwidth / 8);
						//std::cout << "FA " << input2 << " "; 
						break;
					default:
						break;
				}
				
			}
			
			//djn_decrypt(output, pub, prv, enc_d1);
            //gmp_printf("--> %Zd \n", output);
		}

        std::cout << "Average Time: " << timeSpent / NUM_TESTS << " ms." << std::endl << std::endl;
		std::cout << "Average Communication: " << bandwidth/ NUM_TESTS << " bytes." << std::endl << std::endl;
		
		std::cout << "Number of Iterations: " << ctr << std::endl;
		std::cout << "**********************************************************" << std::endl;
		
		NUM_INPUTS++; 
		std::cout << std::endl;
	}
}


int main(int argc, const char * argv[])
{
    unsigned int bandwidth = 0;
    mpz_t p1, p2, p1_enc, p2_enc, res, dcr;
    mpz_inits(p1, p2, p1_enc, p2_enc, res, dcr, NULL);
    
    pub = (djn_pubkey_t*) malloc(1);
    prv = (djn_prvkey_t*) malloc(1);
    
    djn_keygen(2048, &pub, &prv);
    
    //initialize global parameters
    mpz_t zero, one, three, a, b, enc_a, enc_b, enc_res, result;
    mpz_inits(zero, one, three, a, b, enc_res, result, enc_0, enc_1, enc_3, enc_a, enc_b, n_minus_1, NULL);
    
    mpz_set_ui(zero, 0);
    mpz_set_ui(one, 1);
    mpz_set_ui(three, 3);
    
    djn_encrypt(enc_0, pub, zero);
    djn_encrypt(enc_1, pub, one);
    djn_encrypt(enc_3, pub, three);
    
    mpz_sub_ui(n_minus_1, pub->n, 1);
    
    // Testing the equality
    mpz_set_ui(a, 6);
    mpz_set_ui(b, 10);

    djn_encrypt(enc_a, pub, a);
    djn_encrypt(enc_b, pub, b);

    unsigned int bs = 0;
    bandwidth = SecureEqualityProtocol(enc_res, enc_b, enc_a, bs);

    djn_decrypt(result, pub, prv, enc_res);

    gmp_printf("Equal: %Zd\n", result);

    return 0;
}









