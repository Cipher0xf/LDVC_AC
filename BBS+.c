#include <stdio.h>
#include <sys/time.h>
#include <ELiPS/bls12.h>
#include "gmp.h"
#define MAX_L 1001

__uint64_t p;  // order of prime field Zp
g1_t g1;       // base generator of G1
g2_t g2;       // base generator of G2
int L = 1000;   // number of messages to be signed
g1_t h[MAX_L]; // random generators of G1
fr_t x;        // secret key
g2_t w;        // public key
fr_t m[MAX_L]; // messages(integers) to be signed
g1_t B, A;     // signature
fr_t ε, s;
int Disclose[MAX_L];            // whether disclosed(1) or hidden(0)
g1_t A_prime, A_bar, d, π1, π2; // Zero-Knowledge Proof

void init()
{
    srand(time(NULL));
    bls12_init();
    g1_init(&g1);
    g2_init(&g2);
    fr_init(&x);
    g2_init(&w);
    g1_init(&B);
    g1_init(&A);
    fr_init(&ε);
    fr_init(&s);
    g1_init(&A_prime);
    g1_init(&A_bar);
    g1_init(&d);
    g1_init(&π1);
    g1_init(&π2);
    g1_set_random(&g1, state);
    g2_set_random(&g2, state);
    for (int i = 0; i < MAX_L; i++)
    {
        g1_init(&h[i]);
        fr_init(&m[i]);
    }
    memset(Disclose, 0, sizeof(Disclose));
}
void keyGen(int L)
{
    for (int i = 0; i < L + 1; i++)
    {
        g1_set_random(&h[i], state);
    }
    fr_set_random(&x, state);
    g2_scm(&w, &g2, &x); // w=g2^x
    // fr_println("secret-key:\nx=", &x);
    // g2_println("public-key:\nw=", &w);
    // for (int i = 0; i < L + 1; i++)
    // {
    //     printf("h%d=", i);
    //     g1_println("", &h[i]);
    // }
}
void sign(fr_t *m, g1_t *_A, fr_t *_ε, fr_t *_s)
{
    g1_t h0_s, h_m;
    g1_init(&h0_s);
    g1_init(&h_m);
    fr_set_random(_ε, state);
    fr_set_random(_s, state);
    g1_scm(&h0_s, &h[0], _s);
    g1_eca(&B, &g1, &h0_s);
    for (int i = 1; i <= L; i++)
    {
        g1_scm(&h_m, &h[i], &m[i]);
        g1_eca(&B, &B, &h_m);
    } // B=g1·h0^s·Π{1≤i≤L}(hi^mi)
    fr_t exp;
    fr_init(&exp);
    fr_add(&exp, &x, _ε);
    fr_inv(&exp, &exp);
    g1_scm(_A, &B, &exp); // A=B^(1/(x+ε))
}
void sigVf(fr_t *m, g1_t *_A, fr_t *_ε, fr_t *_s)
{
    g3_t left, right;
    g3_init(&left);
    g3_init(&right);
    g2_t temp;
    g2_init(&temp);
    g2_scm(&temp, &g2, _ε);
    g2_eca(&temp, &w, &temp);
    g1g2_to_g3_pairing(&left, _A, &temp);
    g1_t h0_s, h_m;
    g1_init(&h0_s);
    g1_init(&h_m);
    g1_scm(&h0_s, &h[0], _s);
    g1_eca(&B, &g1, &h0_s);
    for (int i = 1; i <= L; i++)
    {
        g1_scm(&h_m, &h[i], &m[i]);
        g1_eca(&B, &B, &h_m);
    } // B=g1·h0^s·Π{1≤i≤L}(hi^mi)
    g1g2_to_g3_pairing(&right, &B, &g2);
    printf("Signature Verification:\n");
    g3_cmp(&left, &right) ? printf("REJECT\n") : printf("ACCEPT\n");
}
void show(fr_t *m, int *Disclose, g1_t *_A, fr_t *_ε, fr_t *_s, g1_t *_A_prime, g1_t *_A_bar, g1_t *_d, g1_t *_π1, g1_t *_π2)
{
    fr_t r1, r2, r3, s_prime, neg_s_prime;
    fr_init(&r1);
    fr_init(&r2);
    fr_init(&r3);
    fr_init(&s_prime);
    fr_init(&neg_s_prime);
    fr_set_random(&r1, state);
    fr_set_random(&r2, state);
    fr_inv(&r3, &r1); // r3=r1^-1
    fr_mul(&s_prime, &r2, &r3);
    fr_neg(&s_prime, &s_prime);
    fr_add(&s_prime, &s_prime, _s); // s'=s-r2·r3
    fr_neg(&neg_s_prime, &s_prime);
    fr_t neg_ε, neg_r2;
    fr_init(&neg_ε);
    fr_init(&neg_r2);
    fr_neg(&neg_ε, _ε);
    fr_neg(&neg_r2, &r2);
    g1_t B_r1, h0_s, h_m, h0_r2, h0_neg_r2, h0_neg_s_prime;
    g1_init(&h0_s);
    g1_init(&h_m);
    g1_scm(&h0_s, &h[0], _s);
    g1_eca(&B, &g1, &h0_s);
    for (int i = 1; i <= L; i++)
    {
        g1_scm(&h_m, &h[i], &m[i]);
        g1_eca(&B, &B, &h_m);
    } // B=g1·h0^s·Π{1≤i≤L}(hi^mi)
    g1_init(&B_r1);
    g1_init(&h0_r2);
    g1_init(&h0_neg_r2);
    g1_scm(_A_prime, _A, &r1); // A'=A^r1
    g1_scm(&B_r1, &B, &r1);
    g1_scm(_A_bar, _A_prime, &neg_ε);
    g1_eca(_A_bar, _A_bar, &B_r1); // A̅=A'^-ε·B^r1
    g1_scm(&h0_neg_r2, &h[0], &neg_r2);
    g1_eca(_d, &B_r1, &h0_neg_r2); // d=B^r1·h0^-r2
    g1_scm(_π1, _A_prime, &neg_ε);
    g1_scm(&h0_r2, &h[0], &r2);
    g1_eca(_π1, _π1, &h0_r2); // π1=A'^-ε·h0^r2
    g1_scm(_π2, _d, &r3);
    g1_scm(&h0_neg_s_prime, &h[0], &neg_s_prime);
    g1_eca(_π2, _π2, &h0_neg_s_prime);
    fr_t neg_m;
    g1_t h_neg_m;
    fr_init(&neg_m);
    g1_init(&h_neg_m);
    for (int i = 1; i <= L; i++)
    {
        if (Disclose[i] == 0)
        {
            fr_neg(&neg_m, &m[i]);
            g1_scm(&h_neg_m, &h[i], &neg_m);
            g1_eca(_π2, _π2, &h_neg_m);
        }
    } // π2=d^r3·h0^-s'·Π{i∈AH}(hi^-mi)
}
void verify(fr_t *m, int *Disclose, g1_t *_A_prime, g1_t *_A_bar, g1_t *_d, g1_t *_π1, g1_t *_π2)
{
    /* (1) signature verification */
    g3_t left, right;
    g3_init(&left);
    g3_init(&right);
    g1g2_to_g3_pairing(&left, _A_prime, &w);
    g1g2_to_g3_pairing(&right, _A_bar, &g2);
    printf("Signature Verification: ");
    g3_cmp(&left, &right) ? printf("REJECT\n") : printf("ACCEPT\n"); // e(A',w)≟e(A̅,g2)

    /* (2) ZKP verification */
    int check_hidden, check_disclosed;
    g1_t temp;
    g1_init(&temp);
    g1_eca(&temp, _π1, _d);
    check_hidden = g1_cmp(_A_bar, &temp); // A̅⁄d≟π1
    g1_set(&temp, &g1);
    g1_t h_m;
    g1_init(&h_m);
    for (int i = 1; i <= L; i++)
    {
        if (Disclose[i] == 1)
        {
            g1_scm(&h_m, &h[i], &m[i]);
            g1_eca(&temp, &temp, &h_m);
        }
    }
    check_disclosed = g1_cmp(&temp, _π2); // g1·Π{i∈AD}(hi^mi)≟π2
    printf("Proof Verification: ");
    (check_hidden || check_disclosed) ? printf("REJECT\n") : printf("ACCEPT\n");
    // printf("%d %d\n", check_hidden, check_disclosed);
}
void flatten()
{
    // TODO: string M --> fr_t m
}
void mapGen();
void reorder();
void printDisclosed(int L)
{
    printf("Disclosed Indexes: ");
    for (int i = 1; i <= L; i++)
    {
        if (Disclose[i] == 1)
        {
            printf("%d ", i);
        }
    }
    printf("\n");
}
void timeMeasure(int L, int num)
{
    printf("Disclose %d/%d\n", num, L);
    init();
    keyGen(L);
    for (int i = 1; i <= L; i++)
    {
        fr_set_random(&m[i], state);
        // printf("m%d:",i);
        // fr_println("",&m[i]);
    }
    memset(Disclose, 0, sizeof(Disclose));
    for (int i = 0; i < num; i++)
    {
        int index = rand() % L + 1;
        while (Disclose[index] == 1)
        {
            index = rand() % L + 1;
        }
        Disclose[index] = 1;
    }
    printDisclosed(L);

    clock_t start, end, total;
    double cost;
    sign(m, &A, &ε, &s);
    
    /* time of show() */
    start = clock();
    show(m, Disclose, &A, &ε, &s, &A_prime, &A_bar, &d, &π1, &π2);
    end = clock();
    cost = (double)(end - start) / CLOCKS_PER_SEC * 1000;
    printf("Show: %.3fms\n", cost);

    /* time of verify() */
    start = clock();
    verify(m, Disclose, &A_prime, &A_bar, &d, &π1, &π2);
    end = clock();
    cost = (double)(end - start) / CLOCKS_PER_SEC * 1000;
    printf("Verify: %.3fms\n", cost);
    printf("\n");
}

int main()
{
    for (int num = 5; num <= 30; num += 5)
    {
        timeMeasure(L, num);
    }
    
    // for (int L = 100; L <= 500; L += 100)
    // {
    //     timeMeasure(L, 30);
    // }

    /* test */
    // init();
    // keyGen(L);
    // sign(m, &A, &ε, &s);
    // sigVf(m, &A, &ε, &s);
    // show(m, Disclose, &A, &ε, &s, &A_prime, &A_bar, &d, &π1, &π2);
    // verify(m, Disclose, &A_prime, &A_bar, &d, &π1, &π2);
    return 0;
}