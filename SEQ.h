//
//  SEQ.hpp
//  AlphaAlgorithm
//
//  Created by gtillem on 14/02/17.
//  Copyright © 2017 gtillem. All rights reserved.
//

#ifndef SEQ_hpp
#define SEQ_hpp

#include <stdio.h>
#include "Paillier.h"
#include <algorithm>
#include <math.h>
#include <iostream>
#include <ctime>

using namespace std;

struct EncNode
{
    mpz_t enc;
    int kappa;
    
    //default constructor
    EncNode ()
    :kappa(0)
    {mpz_init(enc);}
    
    //constructor
    EncNode (mpz_t val, int k)
    :kappa(k)
    {mpz_init_set(enc, val);}
};

class SEQ
{

private:
    int NchooseK (int n, int k);
    void PolyCoeffGen (mpz_t coeff[]);
    
public:
    
    SEQ(Paillier * & p, int l);
    void EqualityTesting(mpz_t r[], mpz_t Ex[], mpz_t Ey[], int count);
    bool CheckResult(mpz_t res[], mpz_t Ex[], mpz_t Ey[], int count);
    void GenerateInput(EncNode * & x, EncNode * & y, mpz_t Ex[], mpz_t Ey[], int numX, int numY);
    void PackEncryptedInput(mpz_t EyP[], mpz_t Ey[], int count, int l);
    
    Paillier * p;
    int length;
    int logL;
};


#endif /* SEQ_hpp */
