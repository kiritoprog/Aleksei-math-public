\\ ============================================================
\\ Numerical verification of Stickelberger's theorem in the form
\\ used by K. Rubin, "Kolyvagin's System of Gauss Sums",
\\ Proposition 1.1(ii):
\\
\\     ( alpha(n,t) ) = theta(n) t        as (fractional) ideals of
\\                                        F(mu_n) = Q(zeta_{pn}),
\\ where
\\     alpha(n,t) = g(n,t,zeta_r)^(sigma_delta - b_n)
\\                = sigma_delta(g) * g^(-b_n)   in  Q(zeta_{pn})^x,
\\     theta(n)   = (1/pn)(sigma_delta - b_n) s(n),
\\     s(n)       = Sum_{(a,pn)=1} a tau_a^{-1},
\\     t          = the prime of Q(zeta_{pn}) above r singled out by
\\                  the character eps_{n,t}(a) = a^{-(r-1)/pn} (mod t).
\\
\\ Written additively, theta(n) t means  prod_c tau_c(t)^{theta_c}
\\ where theta(n) = Sum_c theta_c tau_c,  theta_c = -floor(b_n c^{-1}/pn).
\\
\\ Along the way we also verify the classical factorization that
\\ Rubin's proof cites ([Lang] Ch. 2, Thm. 2.2 / FAC 1):
\\
\\     ( g(n,t,zeta_r)^{pn} ) = t^{s(n)},
\\     i.e.  v_{tau_c(t)}(g^{pn}) = lift(c^{-1} mod pn).
\\
\\ IDENTIFICATION OF t AND ITS CONJUGATES.  With g0 = znprimroot(r)
\\ (the generator used in Eps), eps(g0) = zeta_{pn}^{-1} and Rubin's
\\ congruence eps(a) = a^{-(r-1)/pn} (mod t) force
\\     zeta_{pn} = u (mod t),        u = g0^{(r-1)/pn} mod r,
\\ and then, since u has exact order pn in F_r^x,
\\     zeta_{pn} = u^{ lift(c^{-1} mod pn) }   (mod tau_c(t)).
\\ This is how each conjugate prime is located below.
\\
\\ REQUIRES: scripts_Gausssums_v5.gp loaded first (uses its globals
\\ p, delta, BPREC and its functions Gauss_Sum, Cyclo_Subfield,
\\ Theta_Element, b, delta_pn).  Run e.g.
\\     \r scripts_Gausssums_v5.gp
\\     \r verify_stickelberger_rubin.gp
\\     Verify_Stickelberger_Demo()
\\
\\ CROSS-CHECKED: for p = 5, n = 1, r = 11 (delta = 2, b = 2) the
\\ expected valuations were computed independently (11-adic embeddings
\\ zeta_5 -> Teichmueller lift):  v(g^5) = (1,3,2,4) at c = (1,2,3,4)
\\ and v(alpha^5) = (0,-5,0,-5) = 5*theta_c, theta = -tau_2 - tau_4.
\\ ============================================================

\\ ------------------------------------------------------------
\\ Galois action tau_e : zeta_N -> zeta_N^e on Q(zeta_N), acting by
\\ permutation of monomial exponents (much faster than subst/Horner).
\\ ------------------------------------------------------------
Tau_Cyclo(g, N, e) =
{
    my(P = lift(g), W, Q = 0);
    if(gcd(e, N) > 1, error("Tau_Cyclo: e must be prime to N"));
    if(type(P) != "t_POL", return(Mod(P, polcyclo(N))));
    W = Vecrev(P);
    for(i = 1, #W,
        if(W[i] != 0, Q += W[i] * x^(((i-1)*e) % N)));
    return(Mod(Q, polcyclo(N)));
}

\\ ------------------------------------------------------------
\\ Fast Gauss sum: g = Sum_a eps(a) zeta_r^a with eps(a) =
\\ zeta_{pn}^{-ind(a)}, assembled by pure exponent bookkeeping in
\\ Q(zeta_{pnr}):  zeta_{pn} = x^r, zeta_r = x^{pn}, so the a-th term
\\ is x^{(a*pn - ind(a)*r) mod pnr}.  Agrees with Gauss_Sum(n,r) but
\\ avoids per-term modular powering (essential for large p*n*r).
\\ ------------------------------------------------------------
Gauss_Sum_Fast(n, r) =
{
    my(m = p*n, N = p*n*r, g0, ind, Q = 0);
    if((r-1) % m, error("need r = 1 mod p*n for eps to have order p*n"));
    g0  = znprimroot(r);
    ind = vector(r);                     \\ ind[a] = znlog(a, g0)
    my(v = Mod(1, r));
    for(i = 0, r-2, ind[lift(v)] = i; v *= g0);
    for(a = 1, r-1,
        Q += x^((a*m - ind[a]*r) % N));
    return(Mod(Q, polcyclo(N)));
}

\\ ------------------------------------------------------------
\\ The prime of K = Q(zeta_m) above r whose residue of zeta_m is w,
\\ i.e. the prime containing (zeta_m - w).  dec = idealprimedec(K,r).
\\ ------------------------------------------------------------
Prime_With_Residue(K, dec, r, w) =
{
    for(i = 1, #dec,
        if(nfeltval(K, x - w, dec[i]) > 0, return(dec[i])));
    error("no prime above ", r, " with residue zeta = ", w);
}

\\ Coefficient of tau_c in a group-ring t_MAP (0 if absent).
GR_Coeff(A, c) = if(mapisdefined(A, c), mapget(A, c), 0);

\\ ------------------------------------------------------------
\\ Main verifier.
\\   n : level (1, or squarefree, prime to p, with r = 1 mod pn)
\\   r : auxiliary prime
\\   alphacheck (default 1): additionally compute alpha itself in
\\       Q(zeta_{pnr}) and descend it (round-trip through
\\       Cyclo_Subfield).  Set to 0 for large p*n*r: it needs one
\\       inversion of g in the big field, the expensive step.
\\ Returns [ok_support, ok_classical, ok_rubin] (1 = verified).
\\ ------------------------------------------------------------
Verify_Stickelberger(n, r, alphacheck = 1) =
{
    my(m = p*n, N = p*n*r, g, A, d, beta, Am, K, u, dec, th,
       fa, ok1 = 1, ok2 = 1, ok3 = 1, S = 0, tms);

    if((r-1) % m, error("need r = 1 (mod p*n)"));
    if(n > 1 && (!issquarefree(n) || gcd(n, p) > 1),
        error("n must be squarefree and prime to p"));

    gettime();
    g = Gauss_Sum_Fast(n, r);
    A = Cyclo_Subfield(g^m, N, m);      \\ g^m in Q(zeta_m); ERRORS if
                                        \\ g^m were not in the subfield
    tms = gettime();
    print("  g and g^", m, " in Q(zeta_", m, "):  computed  [", tms, " ms]");

    d    = delta_pn(n);                 \\ sigma_delta on Q(zeta_m)
    beta = b(n);                        \\ b_n = delta mod p^BPREC, = 1 mod n
    Am   = Tau_Cyclo(A, m, d) * A^(-beta);   \\ = alpha(n,t)^m

    K   = nfinit(polcyclo(m));
    u   = lift(Mod(znprimroot(r), r)^((r-1)/m));  \\ zeta_m = u (mod t)
    dec = idealprimedec(K, r);
    th  = Theta_Element(n);             \\ = Rubin's theta(n)

    \\ --- check 1: (alpha) is supported only above r ------------------
    fa = idealfactor(K, Am);
    for(i = 1, matsize(fa)[1], if(fa[i,1].p != r, ok1 = 0));
    print("  (alpha) supported only at primes above r:            ",
          if(ok1, "OK", "FAIL"));

    \\ --- check 2 + 3: valuations at every conjugate tau_c(t) ---------
    \\   classical:  v_{tau_c(t)}(g^m)     = lift(c^{-1} mod m)
    \\   Rubin:      v_{tau_c(t)}(alpha^m) = m * theta_c
    for(c = 1, m,
        if(gcd(c, m) == 1,
            my(ci = lift(Mod(c, m)^(-1)));
            my(w  = lift(Mod(u, r)^ci));
            my(P  = Prime_With_Residue(K, dec, r, w));
            my(tc = GR_Coeff(th, c));
            S += tc;
            if(nfeltval(K, A, P) != ci,
                ok2 = 0;
                print("   classical mismatch at c = ", c));
            my(v = nfeltval(K, Am, P));
            if(v != m*tc,
                ok3 = 0;
                print("   Rubin mismatch at c = ", c,
                      ":  v(alpha^m) = ", v, ",  m*theta_c = ", m*tc))));
    print("  (g^", m, ") = t^{s(n)}   [classical Stickelberger]:       ",
          if(ok2, "OK", "FAIL"));
    print("  (alpha(n,t)) = theta(n)t   [Rubin Prop. 1.1(ii)]:    ",
          if(ok3, "OK", "FAIL"));

    \\ --- global consistency: Norm(alpha^m) = r^{m * deg theta(n)} ----
    print("  Norm(alpha^m) = r^(m*Sum theta_c):                   ",
          if(idealnorm(K, Am) == abs(r^(m*S)), "OK", "FAIL"));

    \\ --- optional: alpha itself lies in Q(zeta_m)  (Prop. 1.1) -------
    if(alphacheck,
        my(ebig  = lift(chinese(Mod(d, m), Mod(1, r))));
        my(alpha = Tau_Cyclo(g, N, ebig) * g^(-beta));
        my(al    = Cyclo_Subfield(alpha, N, m));  \\ ERRORS if not there
        print("  alpha = g^(sigma_delta - b) lies in Q(zeta_", m,
              "), alpha^m consistent:  ", if(al^m == Am, "OK", "FAIL")));

    return([ok1, ok2, ok3]);
}

\\ ------------------------------------------------------------
\\ Demos / test suite.
\\ ------------------------------------------------------------
\\ NOTE: Verify_Stickelberger uses the GLOBALS p, delta (like the rest
\\ of the v5 script), and scripts_Gausssums_v5.gp sets p = 37 at load
\\ time.  The demo below therefore switches to p = 5 itself and
\\ restores the old values afterwards, as Run_Tests_p37 does.
Verify_Stickelberger_Demo() =
{
    my(oldp = p, olddelta = delta);
    p = 5; delta = lift(znprimroot(p));
    print("=== Rubin Prop. 1.1(ii):  (g^{sigma_delta - b_n}) = theta(n)t ===");
    print("p = ", p, ", delta = ", delta);
    iferr(
        Verify_Stickelberger_Demo_body(),
        E,
        p = oldp; delta = olddelta;
        error("demo failed: ", E));
    p = oldp; delta = olddelta;
}

Verify_Stickelberger_Demo_body() =
{
    print("--- n = 1, r = 11 ---");
    Verify_Stickelberger(1, 11);
    print("--- n = 1, r = 31 ---");
    Verify_Stickelberger(1, 31);
    print("--- n = 11, r = 331   (composite level pn = 55) ---");
    Verify_Stickelberger(11, 331);
}

\\ p = 37 (irregular) version, restoring globals afterwards, in the
\\ style of Run_Tests_p37.  The big-field alpha check is skipped:
\\ inverting g in degree phi(5513) = 5328 is the one expensive step.
Verify_Stickelberger_p37() =
{
    my(oldp = p, olddelta = delta);
    p = 37; delta = lift(znprimroot(p));
    print("=== p = 37, n = 1, r = 149 ===");
    iferr(
        Verify_Stickelberger(1, 149, 0),
        E,
        p = oldp; delta = olddelta;
        error("p = 37 verification failed: ", E));
    p = oldp; delta = olddelta;
}

\\ Consistency of the fast Gauss sum with the reference implementation:
Test_Gauss_Sum_Fast() =
{
    my(oldp = p, olddelta = delta, ok);
    p = 5; delta = lift(znprimroot(p));
    iferr(
        ok = (Gauss_Sum_Fast(1,11) == Gauss_Sum(1,11)
           && Gauss_Sum_Fast(1,31) == Gauss_Sum(1,31)),
        E,
        p = oldp; delta = olddelta;
        error("Gauss_Sum_Fast test failed: ", E));
    p = oldp; delta = olddelta;
    print("Gauss_Sum_Fast == Gauss_Sum  (p = 5; (n,r) = (1,11), (1,31)):  ",
          if(ok, "OK", "FAIL"));
}

\\ Example usage:
\\   \r scripts_Gausssums_v5.gp
\\   \r verify_stickelberger_rubin.gp
\\   Test_Gauss_Sum_Fast()
\\   Verify_Stickelberger_Demo()
\\   Verify_Stickelberger_p37()
\\   Verify_Stickelberger(1, 41)          \\ any prime r = 1 (mod p)
\\   Verify_Stickelberger(11, 661, 0)     \\ n = 11, without alpha check
