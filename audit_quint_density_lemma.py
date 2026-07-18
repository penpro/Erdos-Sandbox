from fractions import Fraction
from itertools import combinations_with_replacement, permutations
from math import gcd
import argparse


TARGET = Fraction(157, 300)


def lcm(a, b):
    return a // gcd(a, b) * b


def expectation_for_moduli(moduli):
    """Exact density average E[1/(1+X)] for X=#{i: moduli[i] divides N}."""
    out = Fraction(0, 1)
    n = len(moduli)
    for mask in range(1 << n):
        subset_lcm = 1
        bits = 0
        for i, m in enumerate(moduli):
            if (mask >> i) & 1:
                subset_lcm = lcm(subset_lcm, m)
                bits += 1
        term = Fraction(1, (bits + 1) * subset_lcm)
        out += term if bits % 2 == 0 else -term
    return out


def expand_pattern(coeffs, primes):
    out = []
    for coeff, prime in zip(coeffs, primes):
        out.extend([prime] * coeff)
    return tuple(sorted(out))


def audit_prime_patterns():
    # After replacing each modulus by a prime divisor, only multiplicity patterns
    # of four prime moduli remain. For a fixed pattern, the largest multiplicity
    # is paired with the smallest prime by the rearrangement argument in
    # quintuple_density_notes.md.
    cases = [
        ((4,), (2,)),
        ((3, 1), (2, 3)),
        ((2, 2), (2, 3)),
        ((2, 1, 1), (2, 3, 5)),
        ((1, 1, 1, 1), (2, 3, 5, 7)),
    ]
    best = (Fraction(10, 1), None)
    print("prime-pattern audit")
    for coeffs, primes in cases:
        moduli = expand_pattern(coeffs, primes)
        value = expectation_for_moduli(moduli)
        print(f"  coeffs={coeffs!s:<12} moduli={moduli!s:<14} E={value}")
        if value < best[0]:
            best = (value, moduli)
    print(f"  best={best[0]} at {best[1]}")
    assert best == (TARGET, (2, 2, 3, 5))


def audit_route_b_prime_multisets():
    primes_237 = [2, 3, 5, 7]
    primes_13 = [2, 3, 5, 7, 11, 13]

    print("Route B finite prime-multiset audit")
    for label, primes in [("{2,3,5,7}", primes_237), ("primes <= 13", primes_13)]:
        best = (Fraction(10, 1), None)
        checked = 0
        for moduli in combinations_with_replacement(primes, 4):
            value = expectation_for_moduli(moduli)
            checked += 1
            if value < best[0]:
                best = (value, moduli)
            if value < TARGET:
                raise AssertionError(f"prime multiset below {TARGET}: {moduli} -> {value}")
        print(f"  {label:<12} checked={checked:<3} best={best[0]} at {best[1]}")
    assert best == (TARGET, (2, 2, 3, 5))


def audit_collision_counterexamples():
    examples = [
        ((2, 2, 3, 3), (2, 2, 3, 5)),
        ((2, 3, 11, 11), (2, 3, 11, 13)),
    ]
    print("collision warnings")
    for collided, separated in examples:
        v_collided = expectation_for_moduli(collided)
        v_separated = expectation_for_moduli(separated)
        print(f"  E{collided} = {v_collided} ; E{separated} = {v_separated}")
        assert v_collided > v_separated


def brute_moduli(bound):
    best = (Fraction(10, 1), None)
    checked = 0
    for moduli in combinations_with_replacement(range(2, bound + 1), 4):
        value = expectation_for_moduli(moduli)
        checked += 1
        if value < best[0]:
            best = (value, moduli)
        if value < TARGET:
            raise AssertionError(f"counterexample below {TARGET}: {moduli} -> {value}")
    print(f"brute arbitrary moduli <= {bound}: checked={checked}, best={best[0]} at {best[1]}")


def audit_assignment_rearrangement():
    # Sanity-check the exchange principle on the first few primes and all
    # multiplicity-pattern assignments. This is not the proof, but it catches
    # implementation mistakes in the pattern audit.
    primes = [2, 3, 5, 7, 11, 13]
    patterns = [(4,), (3, 1), (2, 2), (2, 1, 1), (1, 1, 1, 1)]
    print("assignment sanity check")
    for pattern in patterns:
        k = len(pattern)
        local = (Fraction(10, 1), None)
        for prime_tuple in combinations_with_replacement(primes, k):
            if len(set(prime_tuple)) != k:
                continue
            for coeffs in set(permutations(pattern)):
                moduli = expand_pattern(coeffs, prime_tuple)
                value = expectation_for_moduli(moduli)
                if value < local[0]:
                    local = (value, (coeffs, prime_tuple, moduli))
        print(f"  pattern={pattern!s:<12} best={local[0]} at {local[1][2]}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--brute", type=int, default=0, help="also brute-force all moduli up to N")
    args = parser.parse_args()

    audit_prime_patterns()
    audit_route_b_prime_multisets()
    audit_collision_counterexamples()
    audit_assignment_rearrangement()
    if args.brute:
        brute_moduli(args.brute)
    print("RESULT: PASS")


if __name__ == "__main__":
    main()
