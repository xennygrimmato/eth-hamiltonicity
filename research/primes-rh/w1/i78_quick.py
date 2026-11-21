# I7: Gaussian primes a^2+b^2 in a small box near norm x: smallest box side h containing one.
# I8: Pocklington/Maurer: q prime ~ x^theta, least k with 2kq+1 prime (AP of length x^{1-theta}).
import sympy, math, random
random.seed(2)
print("I7 Gaussian boxes")
for x in [10**8,10**10,10**12]:
    worst=0
    for tr in range(20):
        A=random.randint(int((x/2)**0.5)-10**3,int((x/2)**0.5)); B=int(math.isqrt(x-A*A))
        h=1
        while True:
            found=any(sympy.isprime(a*a+b*b) for a in range(A,A+h) for b in range(B,B+h))
            if found: break
            h+=1
        worst=max(worst,h)
    print(f" x=1e{round(math.log10(x))}: worst box side over 20 boxes {worst} (points {worst**2}); log x={math.log(x):.1f}, x^(1/4)={x**0.25:.0f}")
print("I8 least k with 2kq+1 prime")
for x in [10**8,10**10,10**12]:
    for th in [0.5,0.7,0.9]:
        ks=[]
        for tr in range(30):
            q=sympy.nextprime(random.randint(int(x**th),2*int(x**th)))
            k=max(1,x//(2*q))
            k0=k
            while not sympy.isprime(2*k*q+1): k+=1
            ks.append(k-k0)
        print(f" x=1e{round(math.log10(x))} theta={th}: max steps {max(ks)}, mean {sum(ks)/len(ks):.1f}; AP length x^(1-th)={x**(1-th):.0f}")
