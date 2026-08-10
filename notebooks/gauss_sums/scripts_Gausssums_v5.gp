\\ ============================================================
\\
\\ -- explicit computations in PARI/GP for Kolyvagin's system of Gauss sums (K. Rubin)
\\
\\ CONVENTIONS -- checked against Rubin's paper:
\\  * s(n) = Sum_{a mod pn, (a,pn)=1} a tau_a^{-1}         (Rubin, section 1)
\\  * Theta_Element(n) = (1/pn)(sigma_delta - b(n)) s(n) = Rubin's theta(n)
\\  * Gauss_Sum = Sum_{a=1}^{r-1} eps(a) zeta_r^a, NO leading minus,
\\    with eps of order pn -- matches Rubin's g(n,t,zeta_r), eq. (2),(3)
\\  * D_l = Sum_{i=1}^{l-2} i sigma_l^i,  (sigma_l - 1)D_l = (l-1) - N_l,
\\    N_n = Sum_{tau in G_n} tau -- matches Rubin, section 2
\\  * b(n): the script uses the plain lift  b = delta mod p^BPREC, = 1 mod n.
\\    Rubin requires zeta^delta = zeta^{b_n} on mu_{Mpn}, i.e. the
\\    TEICHMULLER lift b_n = omega(delta) mod pM.  The two agree mod p.
\\    Delta_of_n_pure() is independent of this choice; Delta_of_n()
\\    changes by the unit (chi(delta)-b)/(chi(delta)-b').
\\  * Rubin's Corollary 2.6 (D_r theta(nr,chi) = delta(n,r,chi) N_r) assumes
\\    r = 1 (mod n p^2 M).  Empirically l = 1 (mod M) for every l | n
\\    suffices for the scalar congruence below, and Delta_of_n() VERIFIES
\\    the proportionality on every group element, so each run certifies
\\    its own hypothesis.
\\
\\ Verified numerically (exact arithmetic) against:
\\   * |g(eps)|^2 = r  and  sigma_c(g) = eps(c)^{-1} g  for c = 1 mod pn
\\   * g^{pn} in Q(zeta_{pn})  (round-trip through Cyclo_Subfield)
\\   * Theta_Element(n) has coefficient  -floor(b(n)*a^{-1}/pn)  at sigma_a
\\   * e_chi^2 = e_chi, e_chi e_chi' = 0 (mod M)
\\   * e_chi Theta_Element(1) = (chi(delta) - b) B_{1,chi^{-1}} e_chi (mod M)
\\   * Euler relation: pi(theta_{pnl}) = (1 - Frob_l^{-1}) theta_{pn} + ((l-1)/2) N
\\   * D_n theta(n,chi) = delta(n) e_chi N_n (mod M) whenever every prime
\\     l | n satisfies l = 1 (mod M);  fails otherwise (as it must)
\\   * p = 37 irregularity: see Run_Tests_p37() at the end.
\\
\\ ============================================================

p = 37; n = 1; r = 149;
BPREC = 4;   \\ b(n) = delta (mod p^BPREC);  need valuation(M,p) <= BPREC

CoeffVec(P,d) = Col(Vecrev(P,d));

\\ ------------------------------------------------------------
\\ Express g in Q(zeta_N) as an element of Q(zeta_m), m | N.
\\ ------------------------------------------------------------
Cyclo_Subfield(g,N,m) =
{
    my(step, PhiN, Phim, dN, dm, P, cols, A, v, sol, Q);

    if(N % m, error("m must divide N"));

    step = N/m;
    PhiN = polcyclo(N);
    Phim = polcyclo(m);
    dN = poldegree(PhiN);
    dm = poldegree(Phim);

    P = lift(Mod(lift(g), PhiN));

    cols = vector(dm, j, CoeffVec(lift(Mod(x^(step*(j-1)), PhiN)), dN));
    A = matrix(dN, dm, i, j, cols[j][i]);

    v = CoeffVec(P, dN);
    sol = matinverseimage(A, v);

    if(#sol == 0,
        error("Element does not lie in the m-th cyclotomic subfield"));

    Q = sum(j=1, dm, sol[j]*x^(j-1));
    return(Mod(Q, Phim));
}

\\ ------------------------------------------------------------
\\ eps: character of (Z/r)^* of order p*n (requires r = 1 mod p*n),
\\ with values in mu_{pn}; eps(g0) = zeta_{pn}^{-1}, g0 = znprimroot(r).
\\ Gauss_Sum(n,r) = Sum_{a=1}^{r-1} eps(a) zeta_r^a  in Q(zeta_{p*n*r}).
\\ ------------------------------------------------------------
Eps(n,r,a) =
{
    my(zprn = Mod(x, polcyclo(p*r*n)));
    my(zpn = zprn^r);
    return(zpn^(-znlog(a, znprimroot(r))));
}

Gauss_Sum(n,r) =
{
    my(zprn = Mod(x, polcyclo(p*r*n)));
    my(zr = zprn^(p*n));
    if((r-1) % (p*n), error("need r = 1 mod p*n for eps to have order p*n"));
    return(sum(aa=1, r-1, Eps(n,r,aa)*zr^aa));
}

\\ Primitive root modulo p defining delta (kept as an integer).
delta = lift(znprimroot(p));

\\ delta viewed inside Gal(Q(zeta_{p*n})/Q), acting trivially on Q(zeta_n).
delta_pn(n) =
{
    if(n == 1, return(lift(Mod(delta, p))));
    return(lift(chinese(Mod(delta, p), Mod(1, n))));
}

\\ b(n) modulo p^BPREC * n:  b(n) = delta mod p^BPREC and b(n) = 1 mod n.
b(n) =
{
    if(n == 1, return(lift(Mod(delta, p^BPREC))));
    return(lift(chinese(Mod(delta, p^BPREC), Mod(1, n))));
}

\\ ------------------------------------------------------------
\\ Stickelberger element p*n*theta(p*n) as a Map:
\\   key   = exponent u of sigma_u in Gal(Q(zeta_{p*n})/Q)
\\   value = coefficient of sigma_u  (= lift of u^{-1} mod p*n)
\\ so theta = Sum_u {u^{-1}/pn} sigma_u = Sum_a {a/pn} sigma_a^{-1}.
\\ ------------------------------------------------------------
Stickelberger(n) =
{
    my(m = p*n, Sn = Map());
    for(a=1, m,
        if(gcd(a,m)==1,
            my(inv = lift(Mod(a,m)^(-1)));
            mapput(Sn, inv,
                   if(mapisdefined(Sn, inv), mapget(Sn, inv), 0) + a)));
    return(Sn);
}

AddCoeff(M,key,c) =
{
    my(newc = c);
    if(mapisdefined(M,key), newc += mapget(M,key));
    if(newc == 0,
        if(mapisdefined(M,key), mapdelete(M,key)),
        mapput(M,key,newc));
    return(M);
}

\\ Theta_Element(n) = (sigma_{delta} - b(n)) * theta(p*n)  in Z[Gal(Q(zeta_pn)/Q)]
\\ (integral; equals - (b - sigma_b) theta, coefficient -floor(b*a^{-1}/pn) at sigma_a)
Theta_Element(n) =
{
    my(m = p*n, Sn = Stickelberger(n), Thetael = Map());
    my(beta = b(n), delta_m = delta_pn(n));

    for(a=1, m,
        if(gcd(a,m)==1,
            my(c = mapget(Sn,a));
            Thetael = AddCoeff(Thetael, lift(Mod(delta_m*a,m)), c/m);
            Thetael = AddCoeff(Thetael, a, -beta*c/m)));
    return(Thetael);
}

\\ ============================================================
\\ Group-ring utilities.  Group-ring elements are Maps:
\\   key = exponent a of tau_a : zeta_N |-> zeta_N^a,  value = coefficient.
\\ ============================================================
GR_Mul(A,B,N) =
{
    my(C = Map(), KA = Vec(A), KB = Vec(B));
    for(i=1, #KA,
        my(a = KA[i], ca = mapget(A,a));
        for(j=1, #KB,
            my(bkey = KB[j], cb = mapget(B,bkey));
            C = AddCoeff(C, lift(Mod(a*bkey,N)), ca*cb)));
    return(C);
}

GR_ReduceMod(A,N,M) =
{
    my(B = Map(), K = Vec(A));
    for(i=1, #K,
        my(a = K[i]);
        B = AddCoeff(B, lift(Mod(a,N)), Mod(mapget(A,a), M)));
    return(B);
}

GR_Print(A) =
{
    my(K = Vec(A));
    for(i=1, #K, print(mapget(A,K[i]), " * tau_", K[i]));
}

\\ Equality of two group-ring elements (portable: no Mat/== on t_MAP).
GR_Equal(A,B) =
{
    my(KA = Vec(A), KB = Vec(B));
    if(#KA != #KB, return(0));
    for(i=1, #KA,
        if(!mapisdefined(B, KA[i]), return(0));
        if(mapget(A, KA[i]) != mapget(B, KA[i]), return(0)));
    return(1);
}

\\ Teichmueller lift omega(a) mod p^alpha (iterating u -> u^p converges).
TeichLiftMod(a,p,alpha) =
{
    my(PA = p^alpha, u = lift(Mod(a,PA)));
    if(gcd(u,p) != 1, error("TeichLiftMod: a must be prime to p"));
    for(i=1, alpha+2, u = lift(Mod(u,PA)^p));
    return(u);
}

Delta_Element_Alpha(n,alpha,i) =
{
    my(PA = p^alpha);
    my(d = lift(Mod(TeichLiftMod(delta,p,alpha), PA)^i));
    if(n == 1, return(d),
        return(lift(chinese(Mod(d,PA), Mod(1,n)))));
}

\\ e_chi = (1/(p-1)) Sum_i chi^{-1}(delta^i) sigma_delta^i,  chi = omega^k.
Idempotent_OmegaPower_Exact_Alpha(n,k,alpha) =
{
    my(E = Map(), eta = Mod(y, polcyclo(p-1,y)));
    if(znorder(Mod(delta,p)) != p-1,
        error("delta must be a primitive root modulo p"));
    k = lift(Mod(k,p-1));
    for(i=0, p-2,
        my(d = Delta_Element_Alpha(n,alpha,i));
        my(coeff = eta^(-k*i)/(p-1));
        E = AddCoeff(E, d, coeff));
    return(E);
}

Theta_Chi_Exact_Alpha(theta,n,k,alpha) =
    GR_Mul(Idempotent_OmegaPower_Exact_Alpha(n,k,alpha), theta, p^alpha*n);

Theta_Chi_Exact(theta,n,k) = Theta_Chi_Exact_Alpha(theta,n,k,1);

Idempotent_OmegaPower_Mod_Alpha(n,k,alpha,M) =
{
    my(E = Map(), s = valuation(M,p), wdelta);
    if(M != p^s || s < 1, error("M must be a positive power of p"));
    if(znorder(Mod(delta,p)) != p-1,
        error("delta must be a primitive root modulo p"));
    k = lift(Mod(k,p-1));
    wdelta = TeichLiftMod(delta,p,s);
    for(i=0, p-2,
        my(d = Delta_Element_Alpha(n,alpha,i));
        my(coeff = Mod(p-1,M)^(-1) * Mod(wdelta,M)^(-k*i));
        E = AddCoeff(E, d, coeff));
    return(E);
}

Theta_Chi_Mod_Alpha(theta,n,k,alpha,M) =
{
    my(N = p^alpha*n);
    my(thetaM = GR_ReduceMod(theta,N,M));
    my(echi = Idempotent_OmegaPower_Mod_Alpha(n,k,alpha,M));
    return(GR_Mul(echi, thetaM, N));
}

Theta_Chi_Mod(theta,n,k,M) = Theta_Chi_Mod_Alpha(theta,n,k,1,M);

\\ ============================================================
\\ Kolyvagin derivative D_n = prod_{l | n} D_l,  D_l = Sum_{i=1}^{l-2} i sigma_l^i,
\\ sigma_l = znprimroot(l) lifted to Gal(Q(zeta_{pn})/Q(zeta_{pn/l})).
\\ ============================================================
Sigma_l_Exponent(p,n,l) =
{
    my(m = p*n, q = m/l, g = lift(znprimroot(l)));
    return(lift(chinese(Mod(g,l), Mod(1,q))));
}

Apply_D_l(A,p,n,l) =
{
    my(m = p*n, s = Sigma_l_Exponent(p,n,l), B = Map(), K = Vec(A));
    for(j=1, #K,
        my(a = K[j], c = mapget(A,a), cur = Mod(a,m));
        for(i=1, l-2,
            cur *= s;
            B = AddCoeff(B, lift(cur), i*c)));
    return(B);
}

Apply_D_n(theta_chi,p,n) =
{
    my(B = theta_chi, F);
    if(n == 1, return(B));
    if(!issquarefree(n) || gcd(n,p) > 1,
        error("n must be squarefree and prime to p"));
    F = factor(n);
    for(i=1, matsize(F)[1], B = Apply_D_l(B,p,n,F[i,1]));
    return(B);
}

DTheta_Chi(theta_chi,p,n) = Apply_D_n(theta_chi,p,n);

\\ ============================================================
\\ delta(n)  such that  D_n theta(n,chi) = delta(n) e_chi N_n  (mod M)
\\ ============================================================

\\ N_n = prod_{l|n} N_l = Sum_{v in (Z/n)^*} tau_{(1 mod p, v mod n)}
Norm_Element(n) =
{
    my(Nn = Map());
    if(n == 1, mapput(Nn, 1, 1); return(Nn));
    for(v=1, n,
        if(gcd(v,n)==1,
            mapput(Nn, lift(chinese(Mod(1,p), Mod(v,n))), 1)));
    return(Nn);
}

\\ delta(n) mod M, with the script's Theta_Element normalization.
\\ Verifies the proportionality D_n theta(n,chi) = delta(n) * (e_chi N_n)
\\ on EVERY group element (raises an error if the congruence fails).
Delta_of_n(n,k,M) =
{
    my(m = p*n, s = valuation(M,p), F, th, thchi, T, E, Nn, R, keys, dl, t);

    if(M != p^s || s < 1, error("M must be a positive power of p"));
    if(s > BPREC,
        error("valuation(M,p) > BPREC: raise BPREC so that b(n) = delta mod M"));
    if(n > 1,
        if(!issquarefree(n) || gcd(n,p) > 1,
            error("n must be squarefree and prime to p"));
        F = factor(n);
        for(i=1, matsize(F)[1],
            if((F[i,1]-1) % M,
                error(Str("prime ", F[i,1],
                    " | n must satisfy l = 1 mod M = ", M)))));

    th    = Theta_Element(n);
    thchi = Theta_Chi_Mod(th, n, k, M);
    T     = Apply_D_n(thchi, p, n);

    E  = Idempotent_OmegaPower_Mod_Alpha(n, k, 1, M);
    Nn = Norm_Element(n);
    R  = GR_Mul(E, Nn, m);      \\ e_chi * N_n: supported on the whole group,
                                \\ all coefficients are units mod M
    keys = Vec(R);
    if(#keys != eulerphi(m), error("internal error: e_chi*N_n support"));

    dl = if(mapisdefined(T, keys[1]), mapget(T, keys[1]), Mod(0,M));
    dl = dl / mapget(R, keys[1]);
    for(i=1, #keys,
        t = if(mapisdefined(T, keys[i]), mapget(T, keys[i]), Mod(0,M));
        if(t != dl*mapget(R, keys[i]),
            error("D_n theta(n,chi) is NOT a multiple of N_n mod M")));
    \\ T cannot have keys outside (Z/pn)^* = support of R, so we are done.
    return(dl);   \\ Mod(delta(n), M)
}

\\ delta(n) for the *pure* projection e_chi theta(pn):
\\ divides out the twist  chi(delta) - b(n)  (a unit mod p iff chi != omega).
\\ With this normalization  Delta_of_n_pure(1,k,M) = B_{1, chi^{-1}}  (mod M).
Delta_of_n_pure(n,k,M) =
{
    my(s = valuation(M,p), wd, u);
    wd = TeichLiftMod(delta,p,s);
    u  = Mod(wd,M)^k - Mod(b(n),M);        \\ chi(delta) - b
    if(valuation(lift(u),p) > 0,
        error("chi(delta) - b is not a unit: chi must differ from omega"));
    return(Delta_of_n(n,k,M) / u);
}

\\ B_{1,omega^e} mod M  (e != -1 mod p-1), computed with extra precision.
B1_OmegaPow(e,M) =
{
    my(s = valuation(M,p), prec = p^(s+2), tot);
    e = e % (p-1);
    if(e == 0,
        tot = p*(p-1)/2,
        tot = lift(sum(a=1, p-1, a*Mod(TeichLiftMod(a,p,s+2), prec)^e)));
    if(tot % p, error("B_{1,omega^e} is not p-integral (e = -1 mod p-1)"));
    return(Mod(tot/p, M));
}

\\ ============================================================
\\ FAST delta(n): chi-descent + closed-form theta coefficients.
\\
\\ Since tau_delta (e_chi X) = chi(delta) (e_chi X), any element X of the
\\ chi-component is determined by its coefficients at tau_a with a = 1
\\ (mod p), indexed by v = a mod n running over (Z/nZ)^*; and D_n, N_n
\\ act within these phi(n) coordinates.  Moreover the coefficient of
\\ Theta_Element(n) at tau_x is given by the closed form
\\     -floor( b(n) * lift(x^{-1} mod pn) / pn ),
\\ and (e_chi N_n)_a = 1/(p-1) for every a = 1 (mod p).  Hence
\\     delta(n) = (p-1) * (common coefficient of D_n theta(n,chi)).
\\ ============================================================

UnitsModN(n) = if(n == 1, [1], select(v -> gcd(v,n) == 1, [1..n]));

\\ Right-hand side of  delta(n) e_chi N_n = D_n theta(n, chi)  (mod M):
\\ returns the vector X with X[j] = coefficient of D_n theta(n, chi) at
\\ tau_a, a = chinese(1 mod p, U[j] mod n), U = UnitsModN(n).
\\ These phi(n) coefficients determine the whole group-ring element:
\\ the coefficient at tau_{delta^i a} is chi(delta)^{-i} X[j].
RHS_DTheta_Vec(n,k,M) =
{
    my(m = p*n, s = valuation(M,p), F, beta, dm, wd, w, invp1, U, phin,
       pos, X);

    if(M != p^s || s < 1, error("M must be a positive power of p"));
    if(s > BPREC,
        error("valuation(M,p) > BPREC: raise BPREC so that b(n) = delta mod M"));
    if(n > 1,
        if(!issquarefree(n) || gcd(n,p) > 1,
            error("n must be squarefree and prime to p"));
        F = factor(n);
        for(i=1, matsize(F)[1],
            if((F[i,1]-1) % M,
                error(Str("prime ", F[i,1],
                    " | n must satisfy l = 1 mod M = ", M)))));

    beta  = b(n);
    dm    = delta_pn(n);
    wd    = TeichLiftMod(delta,p,s);
    w     = Mod(wd,M)^(-k);              \\ chi^{-1}(delta)
    invp1 = Mod(p-1,M)^(-1);
    U     = UnitsModN(n);
    phin  = #U;
    pos   = vector(n);
    for(j=1, phin, pos[U[j]] = j);

    \\ X[j] = coefficient of e_chi * Theta_Element(n) at tau_a:
    \\ (e_chi theta)_a = (p-1)^{-1} Sum_i chi^{-1}(delta)^i theta_{delta^{-i} a},
    \\ and lift((delta^{-i} a)^{-1}) = delta^i a^{-1} mod m.
    X = vector(phin);
    for(j=1, phin,
        my(a  = if(n==1, 1, lift(chinese(Mod(1,p), Mod(U[j],n)))));
        my(ti = lift(Mod(a,m)^(-1)), tot = Mod(0,M), wi = Mod(1,M));
        for(i=0, p-2,
            tot += wi * (-((beta*ti)\m));
            wi  *= w;
            ti   = (ti*dm) % m);
        X[j] = tot * invp1);

    \\ apply D_l for each prime l | n, acting through (Z/nZ)^*
    if(n > 1,
        for(t=1, matsize(F)[1],
            my(l = F[t,1], g = lift(znprimroot(l)));
            my(sl = if(n/l == 1, g % n,
                       lift(chinese(Mod(g,l), Mod(1,n/l)))));
            my(sinv = lift(Mod(sl,n)^(-1)), R = vector(phin));
            for(j=1, phin,
                my(u = U[j], acc = Mod(0,M));
                for(i=1, l-2,
                    u = (u*sinv) % n;
                    acc += i * X[pos[u]]);
                R[j] = acc);
            X = R));
    return(X);
}

\\ Fast delta(n): checks the RHS is constant over G_n and rescales by
\\ (e_chi N_n)_a = 1/(p-1).  Same conventions and choices as Delta_of_n.
Delta_Fast(n,k,M) =
{
    my(X = RHS_DTheta_Vec(n,k,M));
    for(j=2, #X, if(X[j] != X[1],
        error("D_n theta(n,chi) is NOT a multiple of N_n mod M")));
    return((p-1)*X[1]);
}

\\ Correctness test for the equality  delta(n) e_chi N_n = D_n theta(n,chi):
\\ computes the RHS twice -- fast (chi-descent vector) and slowly (full
\\ t_MAP computation D_n(e_chi Theta_Element(n))) -- and compares them on
\\ ALL phi(pn) coefficients, using coefficient(delta^i a) = chi(delta)^{-i} X[j].
Test_RHS(n,k,M) =
{
    my(m = p*n, s = valuation(M,p), ok = 1, cst = 1);
    gettime();
    my(X = RHS_DTheta_Vec(n,k,M));
    my(tfast = gettime());
    my(T = Apply_D_n(Theta_Chi_Mod(Theta_Element(n), n, k, M), p, n));
    my(tslow = gettime());
    my(U = UnitsModN(n), dm = delta_pn(n));
    my(chid = Mod(TeichLiftMod(delta,p,s), M)^k);

    for(j=1, #U,
        my(a = if(n==1, 1, lift(chinese(Mod(1,p), Mod(U[j],n)))));
        my(key = a, c = X[j]);
        for(i=0, p-2,
            my(tt = if(mapisdefined(T,key), mapget(T,key), Mod(0,M)));
            if(tt != c, ok = 0);
            key = (key*dm) % m;
            c   /= chid));
    for(j=2, #U, if(X[j] != X[1], cst = 0));

    print("RHS = D_n theta(n,chi),  n = ", n, ", chi = omega^", k,
          ", M = ", M);
    print("  fast vector == slow map on all ", (p-1)*#U,
          " coefficients:  ", if(ok, "OK", "FAIL"),
          "   [fast: ", tfast, " ms, slow: ", tslow, " ms]");
    print("  constant over G_n (multiple of N_n):  ",
          if(cst, "OK", "FAIL"));
    if(cst, print("  delta(", n, ") = ", lift((p-1)*X[1]), " mod ", M));
}

\\ ============================================================
\\ Self-tests.  For p = 5 (delta = 2, chi = omega^3, sigma_l = znprimroot(l))
\\ the expected values below were computed independently in exact arithmetic.
\\ ============================================================
Run_Tests() =
{
    my(k = 3, ok = 1);

    print("p = ", p, ", delta = ", delta, ", chi = omega^", k);

    \\ 1. integrality + closed form of Theta_Element
    my(th11 = Theta_Element(11), m11 = 5*11, beta11 = b(11));
    for(a=1, m11,
        if(gcd(a,m11)==1,
            my(t = lift(Mod(a,m11)^(-1)),
               got = if(mapisdefined(th11,a), mapget(th11,a), 0));
            if(got != -floor(beta11*t/m11), ok = 0)));
    print("Theta_Element(11) = (sigma_b - b)theta, integral:  ", if(ok,"OK","FAIL"));

    \\ 2. idempotency mod 25
    my(E = Idempotent_OmegaPower_Mod_Alpha(11,k,1,25));
    print("e_chi^2 = e_chi mod 25:  ",
          if(GR_Equal(GR_Mul(E,E,5*11), E), "OK", "FAIL"));

    \\ 3. delta(1) vs Bernoulli number
    print("delta(1) mod 5   = ", lift(Delta_of_n(1,k,5)),  "   (expected 3)");
    print("delta(1) mod 25  = ", lift(Delta_of_n(1,k,25)), "   (expected 8)");
    print("pure delta(1) mod 25 = ", lift(Delta_of_n_pure(1,k,25)),
          "  = B_{1,omega} = ", lift(B1_OmegaPow(-k,25)), "   (expected 13)");

    \\ 4. delta(n) for n > 1  (l = 1 mod M required)
    print("delta(11)  mod 5  = ", lift(Delta_of_n(11,k,5)),  "   (expected 4)");
    print("delta(31)  mod 5  = ", lift(Delta_of_n(31,k,5)),  "   (expected 0)");
    print("delta(341) mod 5  = ", lift(Delta_of_n(341,k,5)), "   (expected 2)");
    print("delta(101) mod 25 = ", lift(Delta_of_n(101,k,25)),"   (expected 24)");
    print("consistency: 24 mod 5 = 4 = delta(101) mod 5:  ",
          if(lift(Delta_of_n(101,k,5)) == 4, "OK", "FAIL"));

    \\ 5. fast chi-descent agrees with the map computation
    print("Delta_Fast == Delta_of_n at n = 11, 341, 101:  ",
          if(Delta_Fast(11,k,5)   == Delta_of_n(11,k,5)
          && Delta_Fast(341,k,5)  == Delta_of_n(341,k,5)
          && Delta_Fast(101,k,25) == Delta_of_n(101,k,25), "OK", "FAIL"));
    Test_RHS(11, k, 5);
}

Demo() =
{
    print("g(11)^5 in Q(zeta_5):");
    print(Cyclo_Subfield(Gauss_Sum(1,11)^5, 55, 5));
    print("  (expected -66 + 220*z + 110*z^2 + 385*z^3, z = zeta_5)");
    my(th = Theta_Element(1));
    print("Theta_Element(1):"); GR_Print(th);
    print("Theta_Chi_Mod(.,1,3,25):"); GR_Print(Theta_Chi_Mod(th,1,3,25));
}

\\ ============================================================
\\ p = 37 irregularity test.
\\ 37 is irregular: 37 | B_32, i.e. (Herbrand-Ribet) the omega^5-eigenspace
\\ of the class group A of Q(mu_37) is nontrivial, because
\\ B_{1, omega^{-5}} = B_{1, omega^31} = B_32/32 = 0 (mod 37).
\\ Hence for chi = omega^5:
\\   * delta(1) = 0 (mod 37)  -- the Stickelberger element itself detects
\\     nothing at level 1 (theta(1,chi) = 0 mod 37);
\\   * delta(l) is a UNIT mod 37 for suitable auxiliary primes l = 1 (mod 37)
\\     -- Kolyvagin's derivative recovers the information at level l, which
\\     (Rubin, Theorems 4.3/4.4) bounds #(A^chi) by 37, so A^chi = Z/37Z
\\     and the "index" d(n_1) = 1 in Rubin's notation.
\\ Expected values below assume delta = 2, sigma_l = znprimroot(l);
\\ a different choice of generators changes the (unit) values of delta(l),
\\ but not the vanishing/nonvanishing.
\\ ============================================================
Run_Tests_p37_body() =
{
    my(k = 5);
    print("p = ", p, ", delta = ", delta, ", chi = omega^", k, ", M = 37");
    print("B_{1,omega^31} mod 37 = ", lift(B1_OmegaPow(31,37)),
          "   (expected 0: 37 | B_32, irregular pair (37,32))");
    print("delta(1)   mod 37 = ", lift(Delta_Fast(1,k,37)),
          "   (expected 0: irregularity at chi = omega^5)");
    gettime();
    print("delta(149) mod 37 = ", lift(Delta_Fast(149,k,37)),
          "   (expected 14, a unit: derivative class nontrivial)  [",
          gettime(), " ms]");
    print("delta(223) mod 37 = ", lift(Delta_Fast(223,k,37)),
          "   (expected 22, a unit)");
    print("delta(593) mod 37 = ", lift(Delta_Fast(593,k,37)),
          "   (expected 6, a unit)");
    print("control, regular index chi = omega^3:");
    print("delta(1)   mod 37 = ", lift(Delta_Fast(1,3,37)),
          "   (expected 33 = (2^3-2)*B_{1,omega^33} = 6*",
          lift(B1_OmegaPow(33,37)), " mod 37)");
    \\ full slow-vs-fast comparison of the RHS  D_149 theta(149, omega^5):
    Test_RHS(149, k, 37);
}

Run_Tests_p37() =
{
    my(oldp = p, olddelta = delta, oldn = n);
    p = 37; delta = lift(znprimroot(p));
    iferr(Run_Tests_p37_body(),
          E,
          p = oldp; delta = olddelta; n = oldn;
          error("p = 37 tests failed: ", E));
    p = oldp; delta = olddelta; n = oldn;
}

\\ Example usage:
\\   Run_Tests()        \\ p = 5  test suite (expected values included)
\\   Run_Tests_p37()    \\ p = 37 irregularity test (restores p = 5 after)
\\   Demo()
\\   d  = Delta_Fast(149, 5, 37)      \\ fast delta(n)  (after setting p = 37)
\\   X  = RHS_DTheta_Vec(149, 5, 37)  \\ RHS coefficients of D_n theta(n,chi)
\\   Test_RHS(149, 5, 37)             \\ fast vs slow RHS, full comparison
\\   d  = Delta_of_n(11, 3, 5)        \\ slow reference (t_MAP) version
\\   dp = Delta_of_n_pure(11, 3, 5)   \\ delta(n) for the pure e_chi*theta
