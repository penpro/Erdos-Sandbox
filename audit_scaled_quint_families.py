"""Exact finite audits for scaled quintuple residual families in EP488.

This is a scratch/referee helper, not a replacement for the written proof.
For a base set A and its dilates tA, it checks alpha/beta formulas of the form

    alpha_t = alpha_num / (alpha_den_coeff * t - 1),
    beta_t  = beta_num / (beta_den * t).

Since B_A(q + L) = B_A(q) + C over one lcm period, the required inequalities
only need one full period once the period increments are positive. A finite
t-range checker is also included for piecewise families where the alpha witness
changes after a small threshold.
"""

from math import gcd


def lcm(a, b):
    return a // gcd(a, b) * b


def lcm_set(values):
    out = 1
    for value in values:
        out = lcm(out, value)
    return out


def b_prefix_counts(base, upto):
    counts = [0] * (upto + 1)
    count = 0
    for q in range(1, upto + 1):
        if any(q % a == 0 for a in base):
            count += 1
        counts[q] = count
    return counts


def audit_family(name, base, t_min, alpha_num, alpha_den_coeff, beta_num, beta_den):
    m = max(base)
    period = lcm_set(base)
    alpha_q = alpha_den_coeff - 1
    counts = b_prefix_counts(base, max(period, m + period - 1, alpha_q))
    period_count = counts[period]

    alpha_count = counts[alpha_q]
    beta_hits = [
        q for q in range(m, m + period) if beta_den * counts[q] == beta_num * q
    ]

    assert alpha_count == alpha_num, (name, "alpha witness", alpha_q, alpha_count)
    assert beta_hits, (name, "no beta equality witness")

    alpha_slope_increment = alpha_den_coeff * period_count - alpha_num * period
    alpha_tmin_increment = t_min * alpha_slope_increment - period_count
    beta_gap_increment = beta_num * period - beta_den * period_count

    assert alpha_slope_increment >= 0, (name, "alpha slope period increment")
    assert alpha_tmin_increment >= 0, (name, "alpha t_min period increment")
    assert beta_gap_increment >= 0, (name, "beta period increment")
    assert beta_num * alpha_den_coeff < 2 * alpha_num * beta_den, (
        name,
        "ordering-free limit beta < 2*alpha",
    )

    alpha_slope_zeros = []
    for q in range(m, m + period):
        bq = counts[q]

        # For all t >= t_min:
        #   bq / (t(q+1)-1) >= alpha_num / (alpha_den_coeff*t - 1).
        # Equivalently:
        #   t*(alpha_den_coeff*bq - alpha_num*(q+1)) >= bq - alpha_num.
        slope = alpha_den_coeff * bq - alpha_num * (q + 1)
        at_tmin = t_min * slope - (bq - alpha_num)
        assert slope >= 0, (name, "alpha slope", q, bq, slope)
        assert at_tmin >= 0, (name, "alpha at t_min", q, bq, at_tmin)
        if slope == 0:
            alpha_slope_zeros.append((q, bq))

        # For all t, the beta bound is:
        #   bq / (tq) <= beta_num / (beta_den*t).
        assert beta_den * bq <= beta_num * q, (name, "beta", q, bq)

    print(f"{name}: PASS")
    print(f"  base={base}, t_min={t_min}, lcm={period}, period_count={period_count}")
    print(f"  alpha={alpha_num}/({alpha_den_coeff}t-1), witness q={alpha_q}")
    print(f"  beta={beta_num}/({beta_den}t), equality q={beta_hits[:8]}")
    print(f"  alpha slope zeros in first period={alpha_slope_zeros[:8]}")
    print(
        f"  beta/alpha limit={beta_num * alpha_den_coeff}/{beta_den * alpha_num}"
    )
    print(f"  increments: alpha_slope={alpha_slope_increment}, alpha_tmin={alpha_tmin_increment}, beta_gap={beta_gap_increment}")


def audit_family_finite_t_range(
    name, base, t_values, alpha_num, alpha_den_coeff, beta_num, beta_den
):
    m = max(base)
    period = lcm_set(base)
    alpha_q = alpha_den_coeff - 1
    counts = b_prefix_counts(base, max(period, m + period - 1, alpha_q))
    period_count = counts[period]

    alpha_count = counts[alpha_q]
    beta_hits = [
        q for q in range(m, m + period) if beta_den * counts[q] == beta_num * q
    ]

    assert alpha_count == alpha_num, (name, "alpha witness", alpha_q, alpha_count)
    assert beta_hits, (name, "no beta equality witness")

    beta_gap_increment = beta_num * period - beta_den * period_count
    assert beta_gap_increment >= 0, (name, "beta period increment")

    for t in t_values:
        alpha_den_at_t = alpha_den_coeff * t - 1
        alpha_period_increment = (
            period_count * alpha_den_at_t - alpha_num * t * period
        )
        assert alpha_period_increment >= 0, (
            name,
            "alpha period increment",
            t,
            alpha_period_increment,
        )
        assert beta_num * alpha_den_at_t < 2 * alpha_num * beta_den * t, (
            name,
            "ordering-free beta < 2*alpha",
            t,
        )

        for q in range(m, m + period):
            bq = counts[q]

            alpha_gap = bq * alpha_den_at_t - alpha_num * (t * (q + 1) - 1)
            assert alpha_gap >= 0, (name, "alpha", t, q, bq, alpha_gap)

            assert beta_den * bq <= beta_num * q, (name, "beta", t, q, bq)

    t_list = list(t_values)
    print(f"{name}: PASS")
    print(f"  base={base}, t_values={t_list}, lcm={period}, period_count={period_count}")
    print(f"  alpha={alpha_num}/({alpha_den_coeff}t-1), witness q={alpha_q}")
    print(f"  beta={beta_num}/({beta_den}t), equality q={beta_hits[:8]}")
    print(f"  beta_gap_increment={beta_gap_increment}")


def main():
    audit_family(
        name="Q = {4,6,10,14,15}",
        base=[4, 6, 10, 14, 15],
        t_min=1,
        alpha_num=15,
        alpha_den_coeff=40,
        beta_num=1,
        beta_den=2,
    )
    audit_family(
        name="R = {2,3,5,7,11}",
        base=[2, 3, 5, 7, 11],
        t_min=2,
        alpha_num=36,
        alpha_den_coeff=48,
        beta_num=11,
        beta_den=12,
    )
    audit_family(
        name="T = {32,45,48,72,80}",
        base=[32, 45, 48, 72, 80],
        t_min=1,
        alpha_num=8,
        alpha_den_coeff=128,
        beta_num=1,
        beta_den=12,
    )
    audit_family(
        name="U = {16,24,36,40,45}",
        base=[16, 24, 36, 40, 45],
        t_min=1,
        alpha_num=7,
        alpha_den_coeff=64,
        beta_num=7,
        beta_den=48,
    )
    audit_family(
        name="V = {4,5,6,9,14}",
        base=[4, 5, 6, 9, 14],
        t_min=1,
        alpha_num=31,
        alpha_den_coeff=63,
        beta_num=5,
        beta_den=8,
    )
    audit_family(
        name="W = {4,6,9,10,14}",
        base=[4, 6, 9, 10, 14],
        t_min=1,
        alpha_num=16,
        alpha_den_coeff=40,
        beta_num=1,
        beta_den=2,
    )
    audit_family(
        name="X = {12,20,30,45,50}",
        base=[12, 20, 30, 45, 50],
        t_min=1,
        alpha_num=18,
        alpha_den_coeff=132,
        beta_num=9,
        beta_den=50,
    )
    audit_family(
        name="Y = {2,3,5,7,13}",
        base=[2, 3, 5, 7, 13],
        t_min=2,
        alpha_num=36,
        alpha_den_coeff=48,
        beta_num=7,
        beta_den=8,
    )
    audit_family(
        name="Z = {2,3,5,11,13}",
        base=[2, 3, 5, 11, 13],
        t_min=2,
        alpha_num=37,
        alpha_den_coeff=50,
        beta_num=7,
        beta_den=8,
    )
    audit_family(
        name="AA = {2,3,7,11,13}",
        base=[2, 3, 7, 11, 13],
        t_min=2,
        alpha_num=23,
        alpha_den_coeff=32,
        beta_num=7,
        beta_den=8,
    )
    audit_family(
        name="AB = {4,6,7,9,15}",
        base=[4, 6, 7, 9, 15],
        t_min=1,
        alpha_num=29,
        alpha_den_coeff=63,
        beta_num=4,
        beta_den=7,
    )
    audit_family(
        name="AC = {4,6,7,10,15}",
        base=[4, 6, 7, 10, 15],
        t_min=1,
        alpha_num=18,
        alpha_den_coeff=40,
        beta_num=4,
        beta_den=7,
    )
    audit_family(
        name="AD = {4,6,9,10,15}",
        base=[4, 6, 9, 10, 15],
        t_min=1,
        alpha_num=16,
        alpha_den_coeff=40,
        beta_num=1,
        beta_den=2,
    )
    audit_family_finite_t_range(
        name="AE = {4,6,9,11,15}, small scales",
        base=[4, 6, 9, 11, 15],
        t_values=range(1, 9),
        alpha_num=33,
        alpha_den_coeff=75,
        beta_num=17,
        beta_den=33,
    )
    audit_family(
        name="AE = {4,6,9,11,15}, large scales",
        base=[4, 6, 9, 11, 15],
        t_min=9,
        alpha_num=7,
        alpha_den_coeff=16,
        beta_num=17,
        beta_den=33,
    )
    audit_family(
        name="AF = {4,6,9,13,15}",
        base=[4, 6, 9, 13, 15],
        t_min=1,
        alpha_num=10,
        alpha_den_coeff=24,
        beta_num=1,
        beta_den=2,
    )
    audit_family(
        name="AG = {4,6,9,14,15}",
        base=[4, 6, 9, 14, 15],
        t_min=1,
        alpha_num=25,
        alpha_den_coeff=63,
        beta_num=1,
        beta_den=2,
    )
    audit_family(
        name="AH = {4,6,9,15,17}",
        base=[4, 6, 9, 15, 17],
        t_min=1,
        alpha_num=11,
        alpha_den_coeff=27,
        beta_num=1,
        beta_den=2,
    )
    audit_family(
        name="AI = {4,6,9,15,19}",
        base=[4, 6, 9, 15, 19],
        t_min=1,
        alpha_num=11,
        alpha_den_coeff=27,
        beta_num=1,
        beta_den=2,
    )
    audit_family_finite_t_range(
        name="AJ = {4,7,10,15,18}, small scales",
        base=[4, 7, 10, 15, 18],
        t_values=range(1, 3),
        alpha_num=53,
        alpha_den_coeff=124,
        beta_num=11,
        beta_den=21,
    )
    audit_family(
        name="AJ = {4,7,10,15,18}, large scales",
        base=[4, 7, 10, 15, 18],
        t_min=3,
        alpha_num=17,
        alpha_den_coeff=40,
        beta_num=11,
        beta_den=21,
    )
    audit_family_finite_t_range(
        name="AK = {8,10,12,15,18}, t=1",
        base=[8, 10, 12, 15, 18],
        t_values=range(1, 2),
        alpha_num=28,
        alpha_den_coeff=104,
        beta_num=7,
        beta_den=20,
    )
    audit_family(
        name="AK = {8,10,12,15,18}, t>=2",
        base=[8, 10, 12, 15, 18],
        t_min=2,
        alpha_num=12,
        alpha_den_coeff=45,
        beta_num=7,
        beta_den=20,
    )
    audit_family_finite_t_range(
        name="AL = {8,12,15,18,20}, t=1",
        base=[8, 12, 15, 18, 20],
        t_values=range(1, 2),
        alpha_num=17,
        alpha_den_coeff=72,
        beta_num=3,
        beta_den=10,
    )
    audit_family(
        name="AL = {8,12,15,18,20}, t>=2",
        base=[8, 12, 15, 18, 20],
        t_min=2,
        alpha_num=7,
        alpha_den_coeff=30,
        beta_num=3,
        beta_den=10,
    )
    audit_family(
        name="AM = {2,3,5,7,17}",
        base=[2, 3, 5, 7, 17],
        t_min=2,
        alpha_num=36,
        alpha_den_coeff=48,
        beta_num=5,
        beta_den=6,
    )
    audit_family(
        name="AN = {2,3,5,7,19}",
        base=[2, 3, 5, 7, 19],
        t_min=2,
        alpha_num=36,
        alpha_den_coeff=48,
        beta_num=23,
        beta_den=28,
    )
    audit_family_finite_t_range(
        name="AO = {3,4,10,14,22}, t=1",
        base=[3, 4, 10, 14, 22],
        t_values=range(1, 2),
        alpha_num=53,
        alpha_den_coeff=98,
        beta_num=7,
        beta_den=11,
    )
    audit_family_finite_t_range(
        name="AO = {3,4,10,14,22}, middle scales",
        base=[3, 4, 10, 14, 22],
        t_values=range(2, 5),
        alpha_num=47,
        alpha_den_coeff=87,
        beta_num=7,
        beta_den=11,
    )
    audit_family(
        name="AO = {3,4,10,14,22}, large scales",
        base=[3, 4, 10, 14, 22],
        t_min=5,
        alpha_num=21,
        alpha_den_coeff=39,
        beta_num=7,
        beta_den=11,
    )
    audit_family_finite_t_range(
        name="AP = {3,4,10,14,25}, t=1",
        base=[3, 4, 10, 14, 25],
        t_values=range(1, 2),
        alpha_num=53,
        alpha_den_coeff=98,
        beta_num=17,
        beta_den=28,
    )
    audit_family_finite_t_range(
        name="AP = {3,4,10,14,25}, middle scales",
        base=[3, 4, 10, 14, 25],
        t_values=range(2, 5),
        alpha_num=47,
        alpha_den_coeff=87,
        beta_num=17,
        beta_den=28,
    )
    audit_family(
        name="AP = {3,4,10,14,25}, large scales",
        base=[3, 4, 10, 14, 25],
        t_min=5,
        alpha_num=21,
        alpha_den_coeff=39,
        beta_num=17,
        beta_den=28,
    )
    audit_family(
        name="AQ = {3,4,10,22,25}",
        base=[3, 4, 10, 22, 25],
        t_min=1,
        alpha_num=53,
        alpha_den_coeff=99,
        beta_num=17,
        beta_den=28,
    )
    audit_family(
        name="AR = {4,5,6,9,21}",
        base=[4, 5, 6, 9, 21],
        t_min=1,
        alpha_num=31,
        alpha_den_coeff=63,
        beta_num=4,
        beta_den=7,
    )
    audit_family(
        name="AS = {4,6,9,10,22}",
        base=[4, 6, 9, 10, 22],
        t_min=1,
        alpha_num=16,
        alpha_den_coeff=40,
        beta_num=15,
        beta_den=32,
    )
    audit_family(
        name="AT = {4,6,9,10,25}",
        base=[4, 6, 9, 10, 25],
        t_min=1,
        alpha_num=16,
        alpha_den_coeff=40,
        beta_num=15,
        beta_den=32,
    )
    audit_family(
        name="AU = {4,6,9,14,21}",
        base=[4, 6, 9, 14, 21],
        t_min=1,
        alpha_num=25,
        alpha_den_coeff=63,
        beta_num=10,
        beta_den=21,
    )
    audit_family(
        name="AV = {4,6,9,14,22}",
        base=[4, 6, 9, 14, 22],
        t_min=1,
        alpha_num=25,
        alpha_den_coeff=63,
        beta_num=15,
        beta_den=32,
    )
    audit_family(
        name="AW = {4,6,9,15,21}",
        base=[4, 6, 9, 15, 21],
        t_min=1,
        alpha_num=25,
        alpha_den_coeff=63,
        beta_num=10,
        beta_den=21,
    )
    audit_family(
        name="AX = {4,6,9,15,22}",
        base=[4, 6, 9, 15, 22],
        t_min=1,
        alpha_num=25,
        alpha_den_coeff=63,
        beta_num=15,
        beta_den=32,
    )


if __name__ == "__main__":
    main()
