//
//  SEQ.cpp
//  AlphaAlgorithm
//
//  Created by gtillem on 14/02/17.
//  Copyright © 2017 gtillem. All rights reserved.
//

#include "SEQ.h"
//#define PACK_EQ

clock_t startEQ;
clock_t endEQ;

int K = 112; //Security Parameter


SEQ::SEQ(Paillier * & p, int l)
{
    this->p = p;
    length = l;
    logL = log2(length)+1;
}

int SEQ::NchooseK (int n, int k)
{
    if (k == 0)
        return 1;
    
    return (n * NchooseK(n - 1, k - 1)) / k;
}

void SEQ::PolyCoeffGen(mpz_t coeff[])
{
    mpz_t temp[logL+1];
    int num=2;
    mpz_init_set_ui(coeff[0], 1);
    
    for (int i = 1; i < logL + 2; i++)
        mpz_init_set_ui(coeff[i], 0);
    
    mpz_init_set_ui(temp[0], 0);
    for(int i = 1; i < logL+1; i++)
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
                mpz_mod(coeff[j], coeff[j], p->n);
            }
        }
        
    }
}

void SEQ::EqualityTesting(mpz_t r[], mpz_t Ex[], mpz_t Ey[], int count)
{
    mpz_t Rand[count], fact, rand[count];
    signed long lBits;
   
    mpz_t temp;
    mpz_init(temp);
    
    //packing
    mpz_t unpackedx;
    mpz_t packbase;
    mpz_init_set_ui(packbase, 2);
    int np,Rem,Number, numPacks;
    
    mpz_pow_ui(packbase, packbase, length + K + 1);
    Rem = count;
    np = (int)(mpz_sizeinbase(p->n, 2) - 2)/(length + K + 1);
    
    numPacks = count / np;
    if(numPacks == 0 && count != 0)
        numPacks = 1;
    if(numPacks * np < count)
        numPacks++;
    
    // precomputation --------------
    lBits = 1 << length;
    int logL= log2 (length)+1;
    
    int f = logL + 1;
    
    
    mpz_init(fact);
    mpz_fac_ui(fact, f - 1);
    
    mpz_invert(fact, fact, p->n);
    
    
    if (logL % 2 == 1)
    {
        mpz_sub(fact, p->n, fact);
    }
    
    mpz_t coeff[length + 2];
    
    PolyCoeffGen(coeff);
    
    mpz_t n_1;
    
    //***********  Alice ****************
    signed long randL[count], randLi[count][length];
    mpz_t Packedx[int (count/np) + 5];
    mpz_t y[count];
    
#ifdef PACK_EQ
    mpz_t temp1, temp2;
    
    Rem = count;
    int IndexP = -1;
    mpz_t randPack[numPacks];
    
    while(Rem > 0)
    {
        IndexP++;
        
        if (Rem > np)
        {
            Number = np;
            Rem -= np;
        }
        else
        {
            Number = Rem;
            Rem = 0;
        }
        
        mpz_init(rand[np * IndexP]);
        p->get_random(rand[np * IndexP], length + K);
        
        randL[np * IndexP] = mpz_mod_ui(temp, rand[np * IndexP], lBits);
        
        for (int j = 0; j < length; j++)
        {
            randLi[np * IndexP][j]= (randL[np * IndexP] >> j) % 2;
        }
        
        
        mpz_init_set(randPack[IndexP], rand[np * IndexP]);
        for (int i = 1; i < Number; i++)
        {
            mpz_mul(randPack[IndexP], randPack[IndexP], packbase);
            
            mpz_init(rand[np * IndexP + i]);
            p->get_random(rand[np * IndexP + i], length + K);
            
            randL[np * IndexP + i] = mpz_mod_ui(temp, rand[np * IndexP + i], lBits);
            
            for (int j = 0; j < length; j++)
            {
                randLi[np * IndexP + i][j]= (randL[np * IndexP + i] >> j) % 2;
            }
            
            mpz_add(randPack[IndexP] , randPack[IndexP], rand[np * IndexP + i]);
            
        }
    }
    
    for(int i = 0; i < numPacks; i++)
    {
        p->encrypt(Packedx[i], randPack[i]);
        
        mpz_inits(n_1, temp1, temp2, NULL);
        
        mpz_sub_ui(n_1, p->n, 1);
        mpz_powm(temp1, Ey[i], n_1, p->n_sp);
        
        
        mpz_mul(temp2, Ex[i], temp1);
        mpz_mod(temp2, temp2, p->n_sp);
        
        mpz_mul(Packedx[i], Packedx[i], temp2);
        mpz_mod(Packedx[i], Packedx[i], p->n_sp);
        
    }
#else
    
    mpz_t Exyr[count];
    for(int i = 0; i < count; i++)
    {
        mpz_t temp1, temp2;
        mpz_inits(rand[i], Exyr[i], temp1, temp2, n_1, NULL);
        
        p->get_random(rand[i], length + K);
        mpz_add_ui(rand[i], rand[i], 1);
        
        
        p->encrypt(Exyr[i], rand[i]);
        
        mpz_sub_ui(n_1, p->n, 1);
        mpz_powm(temp1, Ey[i], n_1, p->n_sp);
        
        mpz_mul(temp2, Ex[i], temp1);
        mpz_mod(temp2, temp2, p->n_sp);
        
        
        mpz_mul(Exyr[i], Exyr[i], temp2);
        mpz_mod(Exyr[i], Exyr[i], p->n_sp);
        
        
        randL[i] = mpz_mod_ui(temp, rand[i], lBits);
        
        for (int j = 0; j < length; j++)
        {
            randLi[i][j]= (randL[i] >> j) % 2;
        }
    }
    //packing
    // Alice packs Exyr[] in Packedx
    Rem = count;
    np = (int)(mpz_sizeinbase(p->n, 2) - 2)/(length + K + 1);
    
    int IndexP = -1;
    
    while (Rem > 0)
    {
        IndexP++;
        
        if (Rem > np)
        {
            Number = np;
            Rem -= np;
        }
        else
        {
            Number = Rem;
            Rem = 0;
        }
        
        mpz_init_set(Packedx[IndexP], Exyr[np*IndexP]);
        
        for (int i = 1; i < Number; i++)
        {
            mpz_powm(Packedx[IndexP], Packedx[IndexP], packbase, p->n_sp);
            
            mpz_mul(Packedx[IndexP] , Packedx[IndexP], Exyr[np * IndexP + i]);
            mpz_mod(Packedx[IndexP], Packedx[IndexP], p->n_sp);
        }
        
    }
#endif //PACK_EQ
    //*************** End of Alice **************
    
    
    //***********  Bob ****************
    //unpack ********

    mpz_init(unpackedx);
    
    IndexP = numPacks;
    Rem=count;
    for (int i = 0; i < IndexP; i++)
    {
        p->decrypt(unpackedx, Packedx[i]);
        
        if(Rem > np)
        {
            Number = np;
            Rem -= np;
        }
        else
        {
            Number = Rem;
            Rem = 0;
        }
        
        for (int j = Number - 1; j >= 0; j--)
        {
            mpz_init(y[i * np + Number - 1 - j]);
            mpz_div_2exp (y[i * np + Number - 1 - j], unpackedx, j * (length + K + 1));
  
            mpz_mul_2exp (temp, y[i * np + Number - 1 - j], j * (length + K + 1));
            mpz_sub(unpackedx, unpackedx, temp);
        }
    }
    // unpack end ***********

    
    mpz_t EyLi[count][length];
    signed long yL[count];
    mpz_t xyr;
    mpz_init(xyr);
    
    bool yLi[count][length];
    
    for(int i = 0; i < count; i++)
    {
        yL[i] = mpz_mod_ui(temp, y[i], lBits);
        
        for (int j = 0; j < length; j++)
        {
            yLi[i][j] = (yL[i] >> j) % 2;
            
            mpz_init(EyLi[i][j]);
            mpz_set_ui(temp, yLi[i][j]);
            
            p->encrypt(EyLi[i][j], temp);
        }
    }
    //*************** End of Bob **************
    
    
    //***********  Alice ****************
    //Alice compute d=\sum  {randL_i \xor EyLi_i}
    mpz_t Exyr2[count], d[count], dM[count], p1, p0, one, zero;
    
    mpz_inits(p1, p0, NULL);
    
    mpz_init_set_ui(one, 1);
    mpz_init_set_ui(zero, 0);
    
    p->encrypt(p1, one);
    p->encrypt(p0, zero);
    
    for (int i = 0; i < count; i++)
    {
        mpz_init_set(d[i], p0);
        
        //perform xor operation
        for (int j = 0; j < length; j++)
        {
            // if r_j is 0, add E[x - y +r] homomorphically
            if (randLi[i][j]==0)
            {
                mpz_mul(d[i], d[i], EyLi[i][j]);
                mpz_mod(d[i], d[i], p->n_sp);
            }
            // else add E[1 - (x - y +r)] homomorphically
            else
            {
                mpz_powm(temp, EyLi[i][j], n_1, p->n_sp);
                mpz_mul(temp, p1, temp);
                mpz_mod(temp, temp, p->n_sp);
                
                mpz_mul(d[i], d[i], temp);
                mpz_mod(d[i], d[i], p->n_sp);
            }
        }
    }
    
    int logLBits = 1 << logL;
    for(int i = 0; i < count; i++)
    {
        p->get_random(rand[i], logL + K);
        
        mpz_init(Exyr2[i]);
        p->encrypt(Exyr2[i], rand[i]);
        
        mpz_mul(Exyr2[i], Exyr2[i], d[i]);
        mpz_mod(Exyr2[i], Exyr2[i], p->n_sp);
        
        randL[i] = mpz_mod_ui(temp, rand[i], logLBits);
        
        for (int j = 0; j < logL; j++)
        {
            randLi[i][j] = (randL[i] >> j) % 2;
        }
    }
 
    //packing
    mpz_set_ui(packbase, 2);
    mpz_pow_ui(packbase, packbase, logL+K+1);
    
    Rem = count;
    np = (int)(mpz_sizeinbase(p->n, 2) - 2)/(logL + K + 1);
    mpz_t Packedx2[int(count/np) + 5];
    
    IndexP = -1;
    
    while(Rem > 0)
    {
        IndexP++;
        
        if (Rem > np)
        {
            Number = np;
            Rem -= np;
        }
        else
        {
            Number = Rem;
            Rem = 0;
        }
        
        mpz_init_set(Packedx2[IndexP], Exyr2[np * IndexP]);
        for (int i = 1; i < Number; i++)
        {
            mpz_powm(Packedx2[IndexP], Packedx2[IndexP], packbase, p->n_sp);
            
            mpz_mul(Packedx2[IndexP] , Packedx2[IndexP], Exyr2[np * IndexP + i]);
            mpz_mod(Packedx2[IndexP], Packedx2[IndexP], p->n_sp);
        }
    }
    //*************** End of Alice **************
    
    //***********  Bob ****************
    //unpack ********
    Rem=count;
    
    for (int i = 0; i <= IndexP; i++)
    {
        p->decrypt(unpackedx, Packedx2[i]);
        
        if(Rem > np)
        {
            Number = np;
            Rem -= np;
        }
        else
        {
            Number = Rem;
            Rem = 0;
        }
        
        for (int j = Number - 1; j >= 0; j--)
        {
            mpz_init(y[i * np + Number - 1 - j]);
            mpz_div_2exp (y[i * np + Number - 1 - j], unpackedx, j * (logL + K + 1));
            
            mpz_mul_2exp (temp, y[i * np + Number - 1 - j], j * (logL + K + 1));
            mpz_sub(unpackedx, unpackedx, temp);
        }
    }
    
    // unpack end ***********
    
    for (int i=0; i<count;i++)
    {
        yL[i] = mpz_mod_ui(temp, y[i], logLBits);
        
        for (int j = 0; j < logL; j++)
        {
            yLi[i][j] = (yL[i] >> j) % 2;
            
            mpz_set_ui(temp, yLi[i][j]);
            p->encrypt(EyLi[i][j], temp);
        }
    }
    //*************** End of Bob **************
    
    //***********  Alice ****************
    //Alice compute d=\sum  {randL_i \xor EyLi_i}
    
    for(int i = 0; i < count; i++)
    {
        mpz_set(d[i], p0);
        
        for (int j = 0; j < logL; j++)
        {
            if (randLi[i][j]==0)
            {
                mpz_mul(d[i], d[i], EyLi[i][j]);
                mpz_mod(d[i], d[i], p->n_sp);
            }
            else
            {
                mpz_powm(temp, EyLi[i][j], n_1, p->n_sp);
                mpz_mul(temp, p1, temp);
                mpz_mod(temp, temp, p->n_sp);
                
                mpz_mul(d[i], d[i], temp);
                mpz_mod(d[i], d[i], p->n_sp);
            }
            
        }
        mpz_mul(d[i], d[i], p1);
        mpz_mod(d[i], d[i], p->n_sp);
    }
    
    int loglogL= log2(logL)+1;
    
    //Alice additively masks the d with another \kappa bit random number
    for(int i = 0; i < count; i++)
    {
        mpz_inits(Rand[i], dM[i], NULL);
        
        p->get_random(Rand[i], loglogL+K+1);
        
        p->encrypt(dM[i], Rand[i]);
        
        mpz_mul(dM[i], dM[i], d[i]);
        mpz_mod(dM[i], dM[i], p->n_sp);
    }
    
    //packing
    mpz_t dMD[count], DpowerI[count][logL+1];
    mpz_t EDpowerI[count][logL+1];
    
    // Alice packs dM[] in Packedx;
    mpz_set_ui(packbase, 2);
    mpz_pow_ui(packbase, packbase, loglogL+K+1);
    
    Rem = count;
    np = (int)(mpz_sizeinbase(p->n, 2) - 2)/(loglogL + K + 1);
    mpz_t Packedx3[int(count/np) + 5];
    
    IndexP = -1;
    
    while(Rem > 0)
    {
        IndexP++;
        
        if(Rem > np)
        {
            Number = np;
            Rem -= np;
        }
        else
        {
            Number = Rem;
            Rem = 0;
        }
        
        mpz_init_set(Packedx3[IndexP], dM[np * IndexP]);
        for (int i = 1; i < Number; i++)
        {
            mpz_powm(Packedx3[IndexP], Packedx3[IndexP], packbase, p->n_sp);
            
            mpz_mul(Packedx3[IndexP] , Packedx3[IndexP], dM[np * IndexP + i]);
            mpz_mod(Packedx3[IndexP], Packedx3[IndexP], p->n_sp);
        }
        
    }
    //*************** End of Alice **************
    
    //***********  Bob ****************
    
    //unpack ********
    Rem=count;
    
    for (int i = 0; i <= IndexP; i++)
    {
        p->decrypt(unpackedx, Packedx3[i]);
        
        if(Rem > np)
        {
            Number = np;
            Rem -= np;
        }
        else
        {
            Number = Rem;
            Rem = 0;
        }
        
        for (int j = Number - 1; j >= 0; j--)
        {
            mpz_init(dMD[i*np+Number-1-j]);
            mpz_div_2exp (dMD[i*np+Number-1-j], unpackedx, j * (loglogL + K + 1));
            
            mpz_mul_2exp (temp, dMD[i*np+Number-1-j], j * (loglogL + K + 1));
            mpz_sub(unpackedx, unpackedx, temp);
        }
    }
    // unpack end ***********
    
    for(int i = 0; i < count; i++)
    {
        mpz_init_set_ui(DpowerI[i][0], 1);
        
        mpz_init(EDpowerI[i][0]);
        p->encrypt(EDpowerI[i][0], one);
        
        for (int j = 1; j<= logL; j++)
        {
            mpz_inits(DpowerI[i][j], EDpowerI[i][j], NULL);
            
            mpz_mul(DpowerI[i][j], DpowerI[i][j-1], dMD[i]);
            mpz_mod(DpowerI[i][j], DpowerI[i][j], p->n);
            
            p->encrypt(EDpowerI[i][j], DpowerI[i][j]);
        }
    }
    //*************** End of Bob **************
    
    //***********  Alice ****************
    //Alice unmasks EDpowerI with Rand[i]
    mpz_t xr[logL+1], xpoweri[count][logL+1];
    mpz_t ptemp;
    
    for(int i = 0; i < count; i++)
    {
        mpz_inits(xpoweri[i][0], xpoweri[i][1], NULL);
        
        p->encrypt(xpoweri[i][0], one);
        mpz_set(xpoweri[i][1], d[i]);
        
        for (int j = 2; j <= logL; j++)
        {
            mpz_inits(xr[j-1], xpoweri[i][j], NULL);
            mpz_powm(xr[j-1], xpoweri[i][j-1], Rand[i], p->n_sp);
            
            mpz_init_set_ui(ptemp, 1);
            
            for (int z = 0; z < j; z++)
            {
                mpz_mul(ptemp, ptemp, Rand[i]);
                mpz_mod(ptemp, ptemp, p->n);
            }
            
            p->encrypt(temp, ptemp);
            
            
            mpz_powm(temp, temp, n_1, p->n_sp);
            mpz_mul(xpoweri[i][j], EDpowerI[i][j], temp);
            mpz_mod(xpoweri[i][j], xpoweri[i][j], p->n_sp);
            
            
            for (int k = 1; k <= j-1; k++)
            {
                mpz_powm_ui(temp, xr[k], NchooseK(j,k), p->n_sp);
                
                mpz_powm(temp, temp, n_1, p->n_sp);
                mpz_mul(xpoweri[i][j], xpoweri[i][j], temp);
                mpz_mod(xpoweri[i][j], xpoweri[i][j], p->n_sp);
            }
            
            for (int k = 1; k < j; k++)
            {
                mpz_powm(xr[k], xr[k], Rand[i], p->n_sp);
            }
        }
    }
    
    //Alice computes the result
    for (int i=0; i<count;i++)
    {
        mpz_init_set(r[i], p0);
        
        for (int j = 0; j < logL + 1; j++)
        {
            if (mpz_cmp_ui(coeff[logL - j], 0) != 0)
            {
                mpz_powm(temp, xpoweri[i][j], coeff[logL-j], p->n_sp);
                
                mpz_mul(r[i], r[i], temp);
                mpz_mod(r[i], r[i], p->n_sp);
            }
        }
        
        mpz_powm(r[i], r[i], fact, p->n_sp);
    }
}


bool SEQ::CheckResult(mpz_t res[], mpz_t Ex[], mpz_t Ey[], int count)
{
    cout << endl<< "Checking equality testing results..."<<endl;
    
    mpz_t x[count], y[count], r[count];
    bool er = false;
    for(int i = 0; i < count; i++)
    {
        mpz_inits(x[i], y[i], r[i], NULL);
        
        p->decrypt(x[i], Ex[i]);
        p->decrypt(y[i], Ey[i]);
        p->decrypt(r[i], res[i]);
        
        
        //std::cout << '\r'<< std::setw(2) << std::setfill('0') << i+1 <<std::flush;
        gmp_printf("x = %Zd and y = %Zd , r = %Zd\n", x[i], y[i], r[i]);
        
        if((mpz_cmp_ui(r[i], 1) == 0 && mpz_cmp(x[i], y[i]) != 0) || ((mpz_cmp_ui(r[i], 0) == 0) && mpz_cmp(x[i], y[i]) == 0))
        {
            gmp_printf("Error: x = %Zd and y = %Zd , r = %Zd\n", x[i], y[i], r[i]);
            er = true;
        }
    }
    if(er == false)
        cout << endl <<"Equality testing results are verified." << endl;
    
    return er;
}

void SEQ::GenerateInput(EncNode * & x, EncNode * & y, mpz_t Ex[], mpz_t Ey[], int numX, int numY)
{
    
    for(int i = 0; i < numX; i++)
    {
        for(int j = 0; j < numY; j++)
        {
            mpz_init_set(Ex[i * numY + j], x[i].enc);
            mpz_init_set(Ey[i * numY + j], y[j].enc);
        }
    }
}


void SEQ::PackEncryptedInput(mpz_t EyP[], mpz_t Ey[], int count, int l)
{
    mpz_t packbase, res;
    mpz_init(res);
    
    int compsize = K + l + 1;
    int bitsize = (int)(mpz_sizeinbase(p->n, 2) - 2);
    int items_in_pack = bitsize/(compsize);
    
    int numPacks = (int) (count / items_in_pack);
    
    if(numPacks == 0 && count != 0)
        numPacks = 1;
    if(numPacks * items_in_pack < count)
        numPacks++;
    
    
    mpz_init_set_ui(packbase, 2);
    mpz_pow_ui(packbase, packbase, compsize);
    
    int Rem = count;
    int Number;
    
    int IndexP = -1;
    
    while(Rem > 0)
    {
        IndexP++;
        
        if (Rem > items_in_pack)
        {
            Number = items_in_pack;
            Rem -= items_in_pack;
        }
        else
        {
            Number = Rem;
            Rem = 0;
        }
        
        mpz_init_set(EyP[IndexP], Ey[items_in_pack * IndexP]);

        for (int i = 1; i < Number; i++)
        {
            mpz_powm(EyP[IndexP], EyP[IndexP], packbase, p->n_sp);
            
            mpz_mul(EyP[IndexP] , EyP[IndexP], Ey[items_in_pack * IndexP + i]);
            mpz_mod(EyP[IndexP], EyP[IndexP], p->n_sp);
            
        }
    }
}
