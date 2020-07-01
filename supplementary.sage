# Copyright (c) 2020 Rambus Inc.
# All rights reserved.
#
# Supplementary material for ladder paper:
# SAGE Implementation of the two main ladders,
# with optional zero avoidance
proof.arithmetic(false)

def random_nonzero(F):
    """Return a random nonzero element of F"""
    r = F(0)
    while r==F(0): r = F.random_element()
    return r

def setup_ladder(xP,ga,gb):
    """Set up the Montgomery/Joye ladder"""
    # This construction is homogeneous, and so
    # should work even if the multiplies are montmuls.
    r = random_nonzero(xP.parent())
    xP  *= r
    r   *= 1
    
    rr   = r^2
    yP   = 4*((xP^2 + ga*rr)*xP + gb*r*rr)
    xP3  = 3*xP
    m    = xP*xP3 + ga*rr
    xP3 *= yP
    yP   = yP^2
    xRP  = m^2 - xP3
    yR   = 2*m*xRP + yP
    
    return (xRP,yP,yR,m)

def finish_ladder(xPQ,xRQ,yQ,m,ga,gb):
    """
    Finish the ladder and output: xP / Z^2
    Uses the "improved" technique which doesn't require initial x
    But does require ga != 0 and gb != 0
    """
    # Avoid m/2, y/2 by scaling other coordinates
    xPQ *= 4
    xRQ *= 4
    yQ  *= 4
    
    # Recover coordinates multiplied by 3
    xQ  = m^2 - xPQ - xRQ
    xP  = 3*xPQ + xQ  
    xR  = 3*xRQ + xQ
    
    # The way to do this in 5 registers (not counting 3,ga,gb) is to compute
    # xP, xQ, xR, m, yQ
    # xP, xQ, xQ*xR, m, yQ
    # xP, xQ*xR, m, c; have to clobber xQ with the multiply
    # xQ+xR = 3*m^2 - xP
    # xP, xQ*xR, xQ+xR, m, c
    # rest can be done in the obvious way
    c   = 3*yQ - m*xQ
    num = (xP*(xQ+xR) + xQ*xR + 6*c*m) * gb
    den = (3*c^2 - xP*(xQ*xR)) * ga

    # Check curve invariants
    if num^3 != den^2 * ga*gb: return None
    if den == 0: return "Bug or on twist: 0/0!"
    
    # Could now: return xP*num*den
    # fancier version with twist check...
    xP  *= 3*num^2
    den *= 3*num
    if not (den.is_square()): return "On twist!"
    return xP/den
    
def montgomery_ladder_avoid_zero_complete_steps(state,key,steps,ga,gb,safe_steps):
    """
    Montgomery ladder with zero avoidance.
    This performs the part of the ladder that would not be safe without
    the zero-avoidance steps.
    """
    (yP,yQ,yR,m,xQP,xRP,prevswap) = state
    
    dodge = start_dodge = False
    for st in range(steps-safe_steps-1,-1,-1):
        # Step which avoids the neutral point at additional cost
        swap = not bool(key & (1<<st))
        prevswap ^^= swap
        swap ^^= dodge
        
        prevstart = start_dodge
        
        start_dodge = xQP==xRP and not dodge
        if dodge: rotate = not prevswap
        else: rotate = start_dodge
        
        dodge = (dodge and prevswap) or start_dodge
        if prevswap^^rotate:
            # Swap Q,R
            xQP,xRP = xRP,xQP
            yQ,yR = yR,yQ

        xRP = xQP-xRP
        if prevstart:
            # Swap P,R
            (yP,yR) = (yR,yP)
            (xQP,xRP) = (xRP,xQP)
        # Rename
        xRQ = xRP
        
        xRP -= xQP
        if rotate:
            # Swap P,Q
            (xRP,xRQ) = (xRQ,xRP)
            (yP,yQ) = (yQ,yP)
        
        g    = xRQ^2
        xRP *= g
        yP  *= yR*xRQ*g
        k    = yR^2
        l    = yR*yQ
        m    = k+l + 2*xRP
        xRP  = xRP^2 + yP
        xQP  = k*l
        yP  *= k
        
        yQ  = yP - m*xQP
        yR  = yP - m*xRP
            
        prevswap = swap

    if dodge and not prevswap:
        return "infinity!"
        
    if prevswap:
        # Swap Q,R.  Don't need y-coordinates
        (xQP,xRP) = (xRP,xQP)
    
    # Output Q
    return finish_ladder(xQP,xRP,-yP,m,ga,gb)

def montgomery_ladder_avoid_zero(xP,key,steps,ga,gb,safe_steps):
    """
    Montgomery ladder with zero avoidance.
    Performs non-zero-avoidant steps, and then calls zero-avoidant routine.
    """
    key = int(key)
    (xRP,yP,_yR,m) = setup_ladder(xP,ga,gb)
    xQP = 0

    prevswap = False
    for st in range(steps-1,steps-safe_steps-1,-1):
        # Step which doesn't avoid neutral point
        # Cost: 1 condswap, 8M + 3S + 7A
        swap = not bool(key & (1<<st))
        prevswap ^^= swap
        
        if prevswap:
            (xQP,xRP) = (xRP,xQP)
            
        yR   = yP + 2*m*xRP
        E    = xQP - xRP
        F    = yR*E
        G    = E^2
        xRP *= G
        m   *= F
        yP  *= F*G
        H    = yR^2
        K    = H + m
        L    = K + m
        m    = xRP - K
        xRP  = xRP^2 + yP
        xQP  = H*L
        yP  *= H
        
        prevswap = swap
            
    # Expand yQ, yR so we can swap with temp
    # Also this part of ladder uses negated y-coords to save a negation
    m *= -2
    yQ  = yP - m*xQP
    yR  = yP - m*xRP
        
    return montgomery_ladder_avoid_zero_complete_steps(
             (yP,yQ,yR,m,xQP,xRP,prevswap),
             key,steps,ga,gb,safe_steps
         )


def qr_ladder_avoid_zero(xP,key,steps,ga,gb,safe_steps):
    """
    (xQP,xRP,yQ,yR) Montgomery ladder.
    Performs non-zero-avoidant steps, and then calls zero-avoidant routine.
    """
    key = int(key)

    (xRP,yQ,yR,m) = setup_ladder(xP,ga,gb)
    m *= 2
    xQP = 0
    G = xRP^2

    prevswap = False
    for st in range(steps-1,steps-safe_steps-1,-1):
        # Step which doesn't avoid neutral point
        # Multiplies/squares can be parallelized 4 ways
        swap = not bool(key & (1<<st))
        prevswap ^^= swap
        
        if prevswap:
            (xQP,xRP) = (xRP,xQP)
            (yR,yQ) = (yQ,yR)
        
        (xQP, xRP, yQ, yR) = \
            (xQP*G, xRP*G, yQ*yR, yR^2)
        
        # Serial version: total 8M + 3S + 7A
        J = xRP - yQ
        m   = J + xRP - yR
        (za, zb, xQP, yQ2) = \
            (xRP*J, xQP*yR, yR*yQ, J^2)

        xRP = za + zb
        xRQ = xRP - xQP
        yQ3 = xRQ - yQ2
        
        # # Alternative parallel version: total 9M+2S+8A
        # # Adds parallelized 3 ways, for a total round
        # # latency of 3M4 + 3A3
        # J  = xRP - yQ
        # t2 = xQP - yQ
        # t1 = yR  - xRP
        #
        # (za, zc, zb, xQP) = \
        #     (xRP*J,  yQ*J, t2*yR, yQ*yR)
        #
        # m   = J - t1
        # xRQ = za + zb
        # yQ3 = zc + zb
        #
        # xRP = xRQ + xQP # postpone until after mul

        (yQ, yRQ, G) = \
            (yQ3*yR, m*xRQ, xRQ^2)

        yR = yRQ + yQ
        
        prevswap = swap
          
    # Expand yP, yQ, yR so we can swap with temp
    # Also this part of ladder uses negated y-coords to save a negation
    yQ = -yQ
    yP  = yQ + m*xQP
    yR = -yR
          
    return montgomery_ladder_avoid_zero_complete_steps(
           (yP,yQ,yR,m,xQP,xRP,prevswap),
           key,steps,ga,gb,safe_steps
       )
       
def joye_ladder_avoid_zero(xP,key,steps,ga,gb,safe_steps):
    """
    Joye ladder with zero avoidance.
    Unlike the Montgomery version, this uses a unified ladder step
    which performs a few extra tweaks if zero avoidance is necessary.
    """
    key = int(key)
    (xRP,yP,yR,_m) = setup_ladder(xP,ga,gb)
    (xRQ,yQ) = (xRP,yP)

    dodge = prevswap = finish_dodge = False
    for st in range(steps):
        swap = bool(key&1<<st)
        prevswap ^^= swap
        if prevswap: (xRP,xRQ) = (xRQ,xRP)

        safe = st < safe_steps
        if safe:
            # We know that we can't hit zero
            # (unless maybe the input point was on the twist)
            if prevswap: (yP,yQ) = (yQ,yP)
            prevswap = swap
            
        else:
            # Play it safe, check for neutral point
            if dodge: dodge_nxt = not prevswap
            else:     dodge_nxt = xRQ==0
            
            dodge_cur = dodge or dodge_nxt
            if prevswap^^dodge_cur:
                # Swap P,Q
                (yP,yQ) = (yQ,yP)
            prevswap = swap^^dodge_cur^^dodge
            
            # If dodge_cur: swap P,Q again (did y above, must do x)
            # Then swap P,R
            # To swap x, could use:
            #   if dodge_cur: (xRP, xRQ) = (xRQ, xRP-xRQ)
            # But we can do it with no extra regs by:
            xRQ = xRP-xRQ
            if dodge_cur:
                (xRP,xRQ) = (xRQ,xRP)
            xRQ = xRP-xRQ
            if dodge_cur:
                (xRP,xRQ) = (xRQ,xRP)
                (yP,yR) = (yR,yP)
        
        # Ladder body
        yP  *= xRQ
        xRQ  = xRQ^2
        xRP *= xRQ
        yP  *= xRQ
        yP  *= yR
        yQ  *= yR
        h    = yR^2
        m    = h + yQ - 2*xRP
        xRP  = xRP^2 - yP
        yP  *= h
        yQ  *= h
        
        if not safe:
            if dodge:
                # results in swapping Q,R
                xRP,yQ = yQ,xRP
            dodge = dodge_nxt
        
        xRQ  = xRP - yQ
        yQ   = m*yQ + yP
        yR   = m*xRP + yP

    if dodge and not prevswap:
        return "infinity!"
    
    if prevswap:
        # swap P,Q
        (xRP,xRQ) = (xRQ,xRP)
        (yP,yQ)   = (yQ,yP)

    xPQ = xRQ-xRP
    if dodge:
        # swap P,R
        xPQ,xRQ = xRQ,xPQ

    # Output P
    return finish_ladder(xPQ,xRQ,yQ,m,ga,gb)

if __name__ == "__main__":
    for c in range(100):
        while True:
            p = random_prime(2^8,lbound=2^4)
            F = GF(p)
            ga = random_nonzero(F)
            gb = random_nonzero(F)
            try: E = EllipticCurve(F,[ga,gb])
            except ArithmeticError: continue
            q = E.cardinality()
            if gcd(q,6) == 1: break
            
        lgk = 20
        lgks = ceil(log(min([fac for fac,_ in factor(q)]),2)) # largest prime factor
        k = randint(0,2**lgk-1)
        while True:
            P = E.random_element()
            if P != 0*P: break
        Q = (2*k+1)*P
        if Q.is_zero(): xQR = "infinity!"
        else: xQR = Q.xy()[0]
        xQ = joye_ladder_avoid_zero(P.xy()[0],k,lgk,ga,gb,lgks-2)
        if xQ != xQR:
            print("FAIL Joye: k=%d, right=%10s, wrong=%10s, p=%d, q=%d, o=%d"
                % (k,xQR,str(xQ),p,q,P.order()))

        Q = (k+2^lgk)*P
        if Q.is_zero(): xQR = "infinity!"
        else: xQR = Q.xy()[0]
        xQ = montgomery_ladder_avoid_zero(P.xy()[0],k,lgk,ga,gb,lgks-2)
        if xQ != xQR:
            print("FAIL Mont: k=%d, right=%10s, wrong=%10s, p=%d, q=%d, o=%d"
                % (k,xQR,str(xQ),p,q,P.order()))
                
        xQ = qr_ladder_avoid_zero(P.xy()[0],k,lgk,ga,gb,lgks-2)
        if xQ != xQR:
            print("FAIL QR: k=%d, right=%10s, wrong=%10s, p=%d, q=%d, o=%d"
                % (k,xQR,str(xQ),p,q,P.order()))
                
        xP = F.random_element()
        while E.is_x_coord(xP): xP = F.random_element()
        xQ = joye_ladder_avoid_zero(xP,k,lgk,ga,gb,lgks-2)
        if xQ not in ["On twist!", "infinity!", "Bug or on twist: 0/0!"]:
            print("FAIL Joye twist: k=%d, right=%10s, wrong=%10s, p=%d, q=%d, o=%d"
                % (k,xQR,str(xQ),p,q,P.order()))

        xQ = montgomery_ladder_avoid_zero(xP,k,lgk,ga,gb,lgks-2)
        if xQ not in ["On twist!", "infinity!", "Bug or on twist: 0/0!"]:
            print("FAIL Mont twist: k=%d, right=%10s, wrong=%10s, p=%d, q=%d, o=%d"
                % (k,xQR,str(xQ),p,q,P.order()))

        xQ = qr_ladder_avoid_zero(xP,k,lgk,ga,gb,lgks-2)
        if xQ not in ["On twist!", "infinity!", "Bug or on twist: 0/0!"]:
            print("FAIL QR twist: k=%d, right=%10s, wrong=%10s, p=%d, q=%d, o=%d"
                % (k,xQR,str(xQ),p,q,P.order()))