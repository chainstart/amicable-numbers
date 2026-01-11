# Amicable Numbers Formalization in Lean 4

A formal verification of amicable numbers theory in Lean 4 using Mathlib.

## Overview

Two positive integers `m` and `n` are **amicable** if each is the sum of the proper divisors of the other:
- s(m) = n
- s(n) = m

where s(k) = σ(k) - k is the sum of proper divisors of k, and σ is the divisor sum function.

The study of amicable numbers dates back to the ancient Greeks, with the pair (220, 284) known to the Pythagoreans around 500 BC.

## Main Results

### Definitions
- `Nat.properDivisorSum`: Sum of proper divisors of n
- `Nat.IsAmicablePair`: Predicate for amicable pairs
- `Nat.IsAmicable`: Predicate for amicable numbers
- `Nat.thabit`: The Thabit-ibn-Qurra numbers t_n = 3·2^n - 1

### Verified Amicable Pairs
| Pair | Theorem | Discoverer | Year |
|------|---------|------------|------|
| (220, 284) | `isAmicablePair_220_284` | Pythagoreans | ~500 BC |
| (1184, 1210) | `isAmicablePair_1184_1210` | Niccolò Paganini | 1866 |
| (17296, 18416) | `isAmicablePair_17296_18416` | Pierre de Fermat | 1636 |

### Structural Theorems
- `IsAmicablePair.symm`: Amicable pairs are symmetric
- `IsAmicablePair.ne`: Members of an amicable pair are distinct
- `IsAmicablePair.one_lt_left/right`: Members are greater than 1
- `not_isAmicable_prime`: Primes cannot be amicable
- `not_isAmicable_one`: 1 is not amicable

### Connections to Other Number Theory
- `properDivisorSum_eq_sum_divisors_sub`: s(n) = σ(n) - n
- `isAmicablePair_iff_sum_divisors`: Characterization via σ
- `IsAmicablePair.lt_iff`: Relation with abundant/deficient numbers

### The Thabit ibn Qurra Rule
The Thabit rule (9th century) provides a method for generating amicable pairs:
If p = 3·2^(n-1) - 1, q = 3·2^n - 1, and r = 9·2^(2n-1) - 1 are all prime,
then (2^n · p · q, 2^n · r) is an amicable pair.

- `ThabitRuleStatement`: Formal statement of the rule
- `thabit_rule_holds_n2`: Verified for n=2, giving (220, 284)
- `thabit_rule_holds_n4`: Verified for n=4, giving (17296, 18416)
- `thabit_rule_n2`, `thabit_rule_n4`: Arithmetic verifications

### Open Problems (Formal Statements)
- `OddOddAmicableConj`: No odd-odd amicable pairs exist
- `InfinitelyManyAmicableConj`: There are infinitely many amicable pairs
- `NoCoprimeAmicableConj`: No coprime amicable pairs exist

## Project Structure

```
amicable-numbers/
├── Amicable/
│   └── Basic.lean      # Main definitions and theorems
├── Amicable.lean       # Root import file
├── lakefile.toml       # Lake configuration
├── lean-toolchain      # Lean version specification
└── README.md           # This file
```

## Building

```bash
# Install dependencies
lake update

# Build the project
lake build
```

Requires Lean 4 and Mathlib. The project uses Mathlib v4.15.0.

## Mathematical Background

### History of Amicable Numbers

1. **Ancient Greece (~500 BC)**: The Pythagoreans knew the pair (220, 284)
2. **9th century**: Thābit ibn Qurra discovered the rule for generating pairs
3. **1636**: Fermat rediscovered (17296, 18416)
4. **1638**: Descartes found (9363584, 9437056)
5. **1747**: Euler found 60 new pairs
6. **1866**: 16-year-old Niccolò Paganini discovered (1184, 1210)
7. **Present**: Over 1.2 billion pairs are known

### Open Questions

Despite centuries of study, fundamental questions remain:
- Are there infinitely many amicable pairs?
- Do odd-odd amicable pairs exist?
- Do coprime amicable pairs exist?

## References

- [Amicable numbers - Wikipedia](https://en.wikipedia.org/wiki/Amicable_numbers)
- [OEIS A063990 - Amicable numbers](https://oeis.org/A063990)
- [OEIS A259180 - Amicable pairs](https://oeis.org/A259180)
- Thābit ibn Qurra, "On the determination of amicable numbers" (9th century)
- Dickson, L.E., "History of the Theory of Numbers", Vol. 1, Ch. I

## Contributing

Contributions are welcome! Potential areas for extension:
1. Prove the general Thabit rule for all n (currently verified for n=2,4)
2. Verify more amicable pairs from Euler's list (2620, 2924), etc.
3. Prove additional structural properties
4. Connect with Mathlib's `ArithmeticFunction.sigma`
5. Prove properties about the parity of amicable pairs

## License

Apache 2.0
