import Fortune.Literature

namespace Fortune

/-- If `q` is below the left endpoint of the lower interval and `p` lies in that interval,
then `q < p`. -/
theorem q_lt_p_of_lt_leftEndpoint_lower_interval {s q p : Nat}
    (hq_left : q < primorial q - s ^ 2)
    (hlow : primorial q - s ^ 2 < p) :
    q < p :=
  lt_trans hq_left hlow

/-- Tightened lower-interval Theorem 18 variant:
the explicit side condition `q < p` is derivable from endpoint ordering. -/
theorem prime_primorial_sub_of_interval_tight
    {s q p : Nat}
    (hsq : ConsecutivePrimes s q)
    (hp : Nat.Prime p)
    (hq_left : q < primorial q - s ^ 2)
    (hlow : primorial q - s ^ 2 < p)
    (hhigh : p < primorial q - 1) :
    Nat.Prime (primorial q - p) := by
  have hq_lt_p : q < p := q_lt_p_of_lt_leftEndpoint_lower_interval hq_left hlow
  exact prime_primorial_sub_of_interval hsq hp hq_lt_p hlow hhigh

end Fortune
