/-
AI-assisted development: Codex with Piero Borgatta, 2026-09-24.
Exact macros for the cancellation tower. All repetition counts remain parameters.
The repeated expansive word [1,2] transports the even cofactor from 8^r to 9^r.
These identities describe an obstruction to immediate descent, not a proof of Collatz.
-/
import CollatzShadowing.CollatzBridge

namespace CollatzShadowing

/-- The expansive two-step word repeated an arbitrary number of times. -/
def cancellationTowerWord : ℕ → List ℕ
  | 0 => []
  | r + 1 => [1, 2] ++ cancellationTowerWord r

@[simp] theorem cancellationTowerWord_length (r : ℕ) :
    (cancellationTowerWord r).length = 2 * r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [cancellationTowerWord, ih]; omega

/-- One exact expanding block, including its intermediate value. -/
theorem cancellationTower_block {v : ℕ} (hv : 2 ≤ v) (heven : Even v) :
    syracuseExponent (8 * v - 5) = 1 ∧
    S (8 * v - 5) = 12 * v - 7 ∧
    syracuseExponent (12 * v - 7) = 2 ∧
    S (12 * v - 7) = 9 * v - 5 := by
  have hodd1 : Odd (12 * v - 7) := by
    refine ⟨6 * v - 4, ?_⟩
    omega
  have hodd2 : Odd (9 * v - 5) := by
    rcases heven with ⟨t, ht⟩
    refine ⟨9 * t - 3, ?_⟩
    omega
  have h1 := syracuseStep_of_num_eq_two_pow_mul_odd
    (n := 8 * v - 5) (a := 1) (m := 12 * v - 7)
    (by simp only [syracuseNumerator]; omega) hodd1
  have h2 := syracuseStep_of_num_eq_two_pow_mul_odd
    (n := 12 * v - 7) (a := 2) (m := 9 * v - 5)
    (by simp only [syracuseNumerator]; norm_num; omega) hodd2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

/-- Exact symbolic compression of arbitrarily many expansive blocks. -/
theorem cancellationTower_run (r u : ℕ) (hu : 2 ≤ u) (heven : Even u) :
    SyracuseWordMatchesFrom (cancellationTowerWord r) (8 ^ r * u - 5) ∧
    evalSyracuseWord (cancellationTowerWord r) (8 ^ r * u - 5) =
      9 ^ r * u - 5 := by
  induction r generalizing u with
  | zero => simp [cancellationTowerWord, SyracuseWordMatchesFrom, evalSyracuseWord]
  | succ r ih =>
      have hpow : 1 ≤ 8 ^ r := Nat.one_le_pow r 8 (by norm_num)
      have hv : 2 ≤ 8 ^ r * u := by nlinarith
      have hev : Even (8 ^ r * u) := heven.mul_left _
      rcases cancellationTower_block hv hev with ⟨ha, hs, hb, ht⟩
      have hstart : 8 ^ (r + 1) * u - 5 = 8 * (8 ^ r * u) - 5 := by
        rw [pow_succ]; congr 1; ring
      have htail : 9 * (8 ^ r * u) - 5 = 8 ^ r * (9 * u) - 5 := by
        congr 1; ring
      have hmatch : SyracuseWordMatchesFrom [1, 2] (8 ^ (r + 1) * u - 5) := by
        simp only [hstart, SyracuseWordMatchesFrom, ha, hs, hb, and_self]
      have heval : evalSyracuseWord [1, 2] (8 ^ (r + 1) * u - 5) =
          8 ^ r * (9 * u) - 5 := by
        rw [evalSyracuseWord_eq_iterate_of_matches _ _ hmatch]
        simpa [hstart, Function.iterate_succ_apply, hs, ht] using htail
      have hi := ih (9 * u) (by omega) (heven.mul_left 9)
      constructor
      · exact SyracuseWordMatchesFrom_append_of_matches _ _ _ hmatch (by rw [heval]; exact hi.1)
      · rw [cancellationTowerWord, evalSyracuseWord_append, heval, hi.2]
        rw [pow_succ]
        congr 1
        ring

/-- The same compression stated for the actual accelerated orbit. -/
theorem cancellationTower_iterate (r u : ℕ) (hu : 2 ≤ u) (heven : Even u) :
    S^[2 * r] (8 ^ r * u - 5) = 9 ^ r * u - 5 := by
  have h := cancellationTower_run r u hu heven
  rw [evalSyracuseWord_eq_iterate_of_matches _ _ h.1,
    cancellationTowerWord_length] at h
  exact h.2

/-- No value inside a repeated block segment drops below its initial value. -/
theorem cancellationTower_noDrop (r u : ℕ) (hu : 2 ≤ u) (heven : Even u) :
    ∀ j ≤ 2 * r, 8 ^ r * u - 5 ≤ S^[j] (8 ^ r * u - 5) := by
  induction r generalizing u with
  | zero =>
      intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simp
  | succ r ih =>
      have hp : 1 ≤ 8 ^ r := Nat.one_le_pow r 8 (by norm_num)
      have hv : 2 ≤ 8 ^ r * u := by nlinarith
      rcases cancellationTower_block hv (heven.mul_left _) with ⟨ha, hs, hb, ht⟩
      have hstart : 8 ^ (r + 1) * u - 5 = 8 * (8 ^ r * u) - 5 := by
        rw [pow_succ]; congr 1; ring
      have htail : 9 * (8 ^ r * u) - 5 = 8 ^ r * (9 * u) - 5 := by
        congr 1; ring
      intro j hj
      rcases j with _ | j
      · simp
      rcases j with _ | j
      · simpa [hstart, hs] using
          (show 8 * (8 ^ r * u) - 5 ≤ 12 * (8 ^ r * u) - 7 by omega)
      · have hi := ih (9 * u) (by omega) (heven.mul_left 9) j (by omega)
        have hbase : 8 * (8 ^ r * u) - 5 ≤ 8 ^ r * (9 * u) - 5 := by
          rw [← htail]; omega
        simpa [hstart, Function.iterate_succ_apply, hs, ht, htail] using hbase.trans hi

private theorem nine_pow_mod_eight (r : ℕ) : 9 ^ r % 8 = 1 := by
  simp [Nat.pow_mod]

private theorem nine_pow_ge_nine {r : ℕ} (hr : 1 ≤ r) : 9 ≤ 9 ^ r := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have hp : 1 ≤ 9 ^ s := Nat.one_le_pow s 9 (by norm_num)
  rw [pow_succ]
  omega

/-- The phase with residual dyadic exponent 1 exits with exponent exactly 3. -/
theorem cancellationTower_exit_one {r : ℕ} (hr : 1 ≤ r) :
    syracuseExponent (2 * 9 ^ r - 5) = 3 ∧
    S (2 * 9 ^ r - 5) = (3 * 9 ^ r - 7) / 4 := by
  have hmod := nine_pow_mod_eight r
  have hdiv := Nat.mod_add_div (9 ^ r) 8
  have hge := nine_pow_ge_nine hr
  let q := 9 ^ r / 8
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hpow : 9 ^ r = 8 * q + 1 := by dsimp [q]; omega
  have heq : (3 * 9 ^ r - 7) / 4 = 6 * q - 1 := by rw [hpow]; omega
  apply syracuseStep_of_num_eq_two_pow_mul_odd
  · simp only [syracuseNumerator, hpow]; norm_num; omega
  · rw [heq]; exact ⟨3 * q - 1, by omega⟩

/-- The phase with residual dyadic exponent 2 exits through [1,1]. -/
theorem cancellationTower_exit_two {r : ℕ} (hr : 1 ≤ r) :
    syracuseExponent (4 * 9 ^ r - 5) = 1 ∧
    S (4 * 9 ^ r - 5) = 6 * 9 ^ r - 7 ∧
    syracuseExponent (6 * 9 ^ r - 7) = 1 ∧
    S (6 * 9 ^ r - 7) = 9 ^ (r + 1) - 10 := by
  have hmod := nine_pow_mod_eight r
  have hdiv := Nat.mod_add_div (9 ^ r) 8
  have hge := nine_pow_ge_nine hr
  let q := 9 ^ r / 8
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hpow : 9 ^ r = 8 * q + 1 := by dsimp [q]; omega
  have h1 := syracuseStep_of_num_eq_two_pow_mul_odd
    (n := 4 * 9 ^ r - 5) (a := 1) (m := 6 * 9 ^ r - 7)
    (by simp only [syracuseNumerator, hpow]; norm_num; omega)
    (show Odd (6 * 9 ^ r - 7) from ⟨24 * q - 1, by rw [hpow]; omega⟩)
  have h2 := syracuseStep_of_num_eq_two_pow_mul_odd
    (n := 6 * 9 ^ r - 7) (a := 1) (m := 9 ^ (r + 1) - 10)
    (by simp only [syracuseNumerator, pow_succ, hpow]; norm_num; omega)
    (show Odd (9 ^ (r + 1) - 10) from ⟨36 * q - 1, by rw [pow_succ, hpow]; omega⟩)
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

/-- The phase with residual dyadic exponent 3 exits through [1,4]. -/
theorem cancellationTower_exit_three (r : ℕ) :
    syracuseExponent (8 * 9 ^ r - 5) = 1 ∧
    S (8 * 9 ^ r - 5) = 12 * 9 ^ r - 7 ∧
    syracuseExponent (12 * 9 ^ r - 7) = 4 ∧
    S (12 * 9 ^ r - 7) = (9 ^ (r + 1) - 5) / 4 := by
  have hmod := nine_pow_mod_eight r
  have hdiv := Nat.mod_add_div (9 ^ r) 8
  let q := 9 ^ r / 8
  have hpow : 9 ^ r = 8 * q + 1 := by dsimp [q]; omega
  have hend : (9 ^ (r + 1) - 5) / 4 = 18 * q + 1 := by
    rw [pow_succ, hpow]; omega
  have h1 := syracuseStep_of_num_eq_two_pow_mul_odd
    (n := 8 * 9 ^ r - 5) (a := 1) (m := 12 * 9 ^ r - 7)
    (by simp only [syracuseNumerator, hpow]; norm_num; omega)
    (show Odd (12 * 9 ^ r - 7) from ⟨48 * q + 2, by rw [hpow]; omega⟩)
  have h2 := syracuseStep_of_num_eq_two_pow_mul_odd
    (n := 12 * 9 ^ r - 7) (a := 4) (m := (9 ^ (r + 1) - 5) / 4)
    (by simp only [syracuseNumerator, hend, hpow]; norm_num; omega)
    (show Odd ((9 ^ (r + 1) - 5) / 4) from ⟨9 * q, by rw [hend]; omega⟩)
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

/-- Exact retained 3-adic arithmetic at the three exits. -/
theorem cancellationTower_exit_ternary {r : ℕ} (hr : 1 ≤ r) :
    4 * S (2 * 9 ^ r - 5) + 7 = 3 ^ (2 * r + 1) ∧
    S (S (4 * 9 ^ r - 5)) + 10 = 3 ^ (2 * r + 2) ∧
    4 * S (S (8 * 9 ^ r - 5)) + 5 = 3 ^ (2 * r + 2) := by
  have h1 := cancellationTower_exit_one hr
  have h2 := cancellationTower_exit_two hr
  have h3 := cancellationTower_exit_three r
  rw [h1.2, h2.2.1, h2.2.2.2, h3.2.1, h3.2.2.2]
  have hmod := nine_pow_mod_eight r
  have hge := nine_pow_ge_nine hr
  have hp1 : 3 ^ (2 * r + 1) = 3 * 9 ^ r := by
    rw [pow_add, pow_mul]; norm_num; ring
  have hp2 : 3 ^ (2 * r + 2) = 9 ^ (r + 1) := by
    rw [pow_add, pow_mul]; norm_num; rw [pow_succ]
  rw [hp1, hp2, pow_succ]
  omega

/-- The original cancellation source, indexed by its reset precision. -/
def cancellationTowerSource (k : ℕ) : ℕ := (2 ^ (k + 1) - 11) / 3

/-- The first step of every even-indexed cancellation source is exact. -/
theorem cancellationTower_initial {k : ℕ} (hk : 4 ≤ k) (heven : Even k) :
    syracuseExponent (cancellationTowerSource k) = 1 ∧
    S (cancellationTowerSource k) = 2 ^ k - 5 := by
  have hge : 16 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hk
    norm_num at this
    exact this
  have hmod3 : 2 ^ (k + 1) % 3 = 2 := by
    rcases heven with ⟨s, hs⟩
    rw [show k + 1 = 2 * s + 1 by omega, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  have hmod2 : 2 ^ k % 2 = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega : k ≠ 0))
  have hsource : 3 * cancellationTowerSource k + 11 = 2 ^ (k + 1) := by
    dsimp [cancellationTowerSource]
    have hd := Nat.mod_add_div (2 ^ (k + 1) - 11) 3
    rw [pow_succ] at *
    omega
  apply syracuseStep_of_num_eq_two_pow_mul_odd
  · simp only [syracuseNumerator]
    rw [pow_succ] at hsource
    norm_num
    omega
  · apply Nat.odd_iff.mpr
    omega

/-- A strict exponential comparison propagates to every higher exponent. -/
private theorem exponential_comparison {a b r₀ : ℕ}
    (hbase : a * 8 ^ r₀ < b * 9 ^ r₀) :
    ∀ r, r₀ ≤ r → a * 8 ^ r < b * 9 ^ r := by
  intro r hr
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction d with
  | zero => simpa using hbase
  | succ d ih =>
      rw [show r₀ + (d + 1) = (r₀ + d) + 1 by omega,
        pow_succ, pow_succ]
      have ih' := ih (by omega)
      calc
        a * (8 ^ (r₀ + d) * 8) = 8 * (a * 8 ^ (r₀ + d)) := by ring
        _ < 8 * (b * 9 ^ (r₀ + d)) := Nat.mul_lt_mul_of_pos_left ih' (by norm_num)
        _ ≤ 9 * (b * 9 ^ (r₀ + d)) := Nat.mul_le_mul_right _ (by norm_num)
        _ = b * (9 ^ (r₀ + d) * 9) := by ring

/-- Uniform comparisons used at the three terminal phases. -/
theorem cancellationTower_growth_comparisons {r : ℕ} (hr : 9 ≤ r) :
    16 * 8 ^ r < 9 * 9 ^ r ∧ 64 * 8 ^ r < 27 * 9 ^ r := by
  constructor
  · exact exponential_comparison (r₀ := 9) (by norm_num) r hr
  · exact exponential_comparison (r₀ := 9) (by norm_num) r hr

/-- All three terminal endpoints exceed the corresponding initial source.
The source formula is meaningful for the admissible even-indexed phases;
this inequality itself holds for every repetition count at least nine. -/
theorem cancellationTower_exit_above_source {r : ℕ} (hr : 9 ≤ r) :
    (4 * 8 ^ r - 11) / 3 < (3 * 9 ^ r - 7) / 4 ∧
    (8 * 8 ^ r - 11) / 3 < 9 ^ (r + 1) - 10 ∧
    (16 * 8 ^ r - 11) / 3 < (9 ^ (r + 1) - 5) / 4 := by
  rcases cancellationTower_growth_comparisons hr with ⟨h1, h3⟩
  have h8 : 2 ≤ 8 ^ r := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ (8 : ℕ)) hr
    norm_num at h
    omega
  have h9 : 9 ≤ 9 ^ r := nine_pow_ge_nine (by omega)
  have hmod := nine_pow_mod_eight r
  rw [pow_succ]
  omega

/-- The complete macro length, including the initial reset and terminal exit. -/
def cancellationTowerMacroLength (r h : ℕ) : ℕ :=
  2 * r + if h = 1 then 2 else 3

/-- Universal no-descent through the entire cancellation macro, including exit.
No repetition count is bounded above and no finite orbit search is used. -/
theorem cancellationTower_full_noDrop {r h : ℕ} (hr : 9 ≤ r)
    (hhlo : 1 ≤ h) (hhhi : h ≤ 3) (heven : Even (3 * r + h)) :
    ∀ j ≤ cancellationTowerMacroLength r h,
      cancellationTowerSource (3 * r + h) ≤
        S^[j] (cancellationTowerSource (3 * r + h)) := by
  let n := cancellationTowerSource (3 * r + h)
  have hk : 4 ≤ 3 * r + h := by omega
  have hinit := cancellationTower_initial hk heven
  have hp : 2 ^ (3 * r + h) = 8 ^ r * 2 ^ h := by
    rw [pow_add, pow_mul]; norm_num
  have hu : 2 ≤ 2 ^ h := by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hhlo
    simpa using this
  have hueven : Even (2 ^ h) := even_iff_two_dvd.mpr
    (dvd_pow_self 2 (by omega : h ≠ 0))
  have hinit' : S n = 8 ^ r * 2 ^ h - 5 := by
    simpa [n, hp] using hinit.2
  have h8 : 2 ≤ 8 ^ r := by
    have hh := Nat.pow_le_pow_right (by norm_num : 1 ≤ (8 : ℕ)) hr
    norm_num at hh
    omega
  have hn : n ≤ 8 ^ r * 2 ^ h - 5 := by
    dsimp [n, cancellationTowerSource]
    rw [pow_succ, hp]
    have : 4 ≤ 8 ^ r * 2 ^ h := by nlinarith
    omega
  have hprefix : ∀ j ≤ 2 * r + 1, n ≤ S^[j] n := by
    intro j hj
    cases j with
    | zero => simp
    | succ j =>
        rw [Function.iterate_succ_apply, hinit']
        exact hn.trans (cancellationTower_noDrop r (2 ^ h) hu hueven j (by omega))
  have hend : S^[2 * r + 1] n = 9 ^ r * 2 ^ h - 5 := by
    rw [Function.iterate_succ_apply, hinit']
    exact cancellationTower_iterate r (2 ^ h) hu hueven
  have hsource : n = (2 * (8 ^ r * 2 ^ h) - 11) / 3 := by
    dsimp [n, cancellationTowerSource]
    rw [pow_succ, hp]
    congr 2
    ring
  have hends := cancellationTower_exit_above_source hr
  intro j hj
  change n ≤ S^[j] n
  by_cases hjpre : j ≤ 2 * r + 1
  · exact hprefix j hjpre
  interval_cases h
  · have hterm := cancellationTower_exit_one (r := r) (by omega)
    have hj' : j = 2 * r + 1 + 1 := by
      simp [cancellationTowerMacroLength] at hj; omega
    have hexit : S^[2 * r + 1 + 1] n = (3 * 9 ^ r - 7) / 4 := by
      rw [Function.iterate_succ_apply', hend]
      simpa [Nat.mul_comm] using hterm.2
    rw [hj', hexit]
    have hnphase : n = (4 * 8 ^ r - 11) / 3 := by
      rw [hsource]; norm_num; congr 2; ring
    rw [hnphase]
    exact hends.1.le
  · have hterm := cancellationTower_exit_two (r := r) (by omega)
    have hexit1 : S^[2 * r + 1 + 1] n = 6 * 9 ^ r - 7 := by
      rw [Function.iterate_succ_apply', hend]
      simpa [Nat.mul_comm] using hterm.2.1
    have hexit2 : S^[2 * r + 1 + 1 + 1] n = 9 ^ (r + 1) - 10 := by
      rw [Function.iterate_succ_apply', hexit1, hterm.2.2.2]
    change j ≤ 2 * r + 3 at hj
    have hj' : j = 2 * r + 1 + 1 ∨ j = 2 * r + 1 + 1 + 1 := by omega
    rcases hj' with rfl | rfl
    · rw [hexit1]
      have hh := hprefix (2 * r + 1) (by omega)
      rw [hend] at hh
      have hg := nine_pow_ge_nine (r := r) (by omega)
      norm_num at hh
      omega
    · rw [hexit2]
      have hnphase : n = (8 * 8 ^ r - 11) / 3 := by
        rw [hsource]; norm_num; congr 2; ring
      rw [hnphase]
      exact hends.2.1.le
  · have hterm := cancellationTower_exit_three r
    have hexit1 : S^[2 * r + 1 + 1] n = 12 * 9 ^ r - 7 := by
      rw [Function.iterate_succ_apply', hend]
      simpa [Nat.mul_comm] using hterm.2.1
    have hexit2 : S^[2 * r + 1 + 1 + 1] n = (9 ^ (r + 1) - 5) / 4 := by
      rw [Function.iterate_succ_apply', hexit1, hterm.2.2.2]
    change j ≤ 2 * r + 3 at hj
    have hj' : j = 2 * r + 1 + 1 ∨ j = 2 * r + 1 + 1 + 1 := by omega
    rcases hj' with rfl | rfl
    · rw [hexit1]
      have hh := hprefix (2 * r + 1) (by omega)
      rw [hend] at hh
      have hg := nine_pow_ge_nine (r := r) (by omega)
      norm_num at hh
      omega
    · rw [hexit2]
      have hnphase : n = (16 * 8 ^ r - 11) / 3 := by
        rw [hsource]; norm_num; congr 2; ring
      rw [hnphase]
      exact hends.2.2.le

/-- Every even precision k≥30 has the complete universal no-descent macro. -/
theorem cancellationTower_noDrop_of_even_ge_thirty {k : ℕ}
    (hk : 30 ≤ k) (heven : Even k) :
    ∀ j ≤ cancellationTowerMacroLength ((k - 1) / 3) (k - 3 * ((k - 1) / 3)),
      cancellationTowerSource k ≤ S^[j] (cancellationTowerSource k) := by
  have hdiv := Nat.mod_add_div (k - 1) 3
  have hmod := Nat.mod_lt (k - 1) (by norm_num : 0 < 3)
  have heq : 3 * ((k - 1) / 3) + (k - 3 * ((k - 1) / 3)) = k := by omega
  have h := cancellationTower_full_noDrop
    (r := (k - 1) / 3) (h := k - 3 * ((k - 1) / 3))
    (by omega) (by omega) (by omega) (by simpa only [heq] using heven)
  simpa only [heq] using h

/-- An explicit cancellation source survives every prescribed finite horizon.
This is an infinite-family consequence of the macro theorem, not a finite test. -/
theorem cancellationTower_noDrop_for_any_horizon (B : ℕ) :
    ∀ j ≤ B, cancellationTowerSource (6 * B + 30) ≤
      S^[j] (cancellationTowerSource (6 * B + 30)) := by
  have h := cancellationTower_noDrop_of_even_ge_thirty
    (k := 6 * B + 30) (by omega) ⟨3 * B + 15, by omega⟩
  intro j hj
  apply h j
  dsimp [cancellationTowerMacroLength]
  have hd := Nat.mod_add_div (6 * B + 30 - 1) 3
  have hm := Nat.mod_lt (6 * B + 30 - 1) (by norm_num : 0 < 3)
  split_ifs <;> omega

/-- Infinitely many cancellation sources lie in the first covered odd port.
This purely arithmetic statement does not depend on the section module. -/
theorem cancellationTowerSource_mod_eighteen (t : ℕ) :
    cancellationTowerSource (18 * t + 10) % 18 = 13 := by
  have hp : 2 ^ (18 * t + 11) % 54 = 50 := by
    induction t with
    | zero => norm_num
    | succ t ih =>
        rw [show 18 * (t + 1) + 11 = (18 * t + 11) + 18 by omega,
          pow_add, Nat.mul_mod, ih]
        norm_num
  have hd := Nat.mod_add_div (2 ^ (18 * t + 11)) 54
  have heq : 18 * t + 10 + 1 = 18 * t + 11 := by omega
  dsimp [cancellationTowerSource]
  rw [heq]
  omega

end CollatzShadowing
