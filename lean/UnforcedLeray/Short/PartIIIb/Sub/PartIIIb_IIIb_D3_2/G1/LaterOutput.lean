import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.Org

/-!
# `ORG:D3/2/G1/5`: the later output (source 4432-4460)

`momentC` (YoungFlat.lean:163) is `∫_{s>0} χ_o s^{-3/2-k/2} (1/c)∫_cell |M_B| ds`, `M_B =
Mcell s (ξ_B s)`.  Since `χ_o = 0` below `1.2/ν`, split at `H = 2/ν` (4501-4508):

* band `0 < s ≤ H`: the frozen-pair/uniform boundedness of the finite band (4376-4412) with the
  uniform Biot-Savart and moment embedding (4443-4450);
* tail `s > H`: `ξ_B(s) = s^{-μ} 𝒰(s,H) D_H`; propagation of the state at `H` to the long-clock age
  `b` by `eq:short-causal-long-forward` (`FullClockLongForward`, 4443-4448), then the impulse
  estimates `eq:ct-tested-impulse`, `eq:ct-absolute-impulse` (3272-3289) at `r = b`, giving
  `C_K |F_+(H,0)|⁻¹‖w(H)‖` after division by `|N_ν|ν^{3+2μ}/c` (4449-4455), the factor `ν^k` from
  `s^{-k/2}` (4421-4439).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

open ConcreteYF

namespace G1

namespace LaterOutput

/-- The right side of `eq:young-later-output` (4454) times `ν^k` (for the tail `s > H = 2/ν`). -/
def rhs (D : SeqData) (S : ℕ → FlatSetting) (n k : ℕ) (z : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) :
    ℝ :=
  (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) / (S n).c) *
    nu D n ^ k * (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ *
      ‖duhamel (S n).pk (D.mu n z : ℂ) ((S n).gB B) (2 / nu D n)‖)

/-- The canonical tested-norm right-hand side for the finite-band estimate on `0 < s ≤ 2/ν`
(source lines 4412, 4677-4694). -/
def rhsTested (D : SeqData) (S : ℕ → FlatSetting) (n k : ℕ) (z : ℝ)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) / (S n).c) *
    nu D n ^ k *
      testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ) (1.1 / nu D n)
        ((S n).gB B)

/-- The integrand of `momentC` (YoungFlat.lean:163). -/
def integrand (D : SeqData) (S : ℕ → FlatSetting) (n k : ℕ) (z : ℝ)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) : ℝ :=
  (S n).chiO s * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
    cellInt (S n).c (fun p => matNorm ((S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) p))

/-- **Band** `0 < s ≤ H = 2/ν` (source 4376-4412, 4443-4450, 4677-4694): the integrand is integrable
there and its integral is at most `C · rhsTested`, uniformly for large `n`, `k ≤ 1`, `z ∈ [-1,1]`
and `B ∈ 𝓑_a`. -/
def BandBound (D : SeqData) : Prop :=
  ForActual D fun S =>
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ n ≥ N, ∀ k : ℕ, k ≤ 1 → ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ B, IsBclass D.K.as (nu D n) B →
        IntegrableOn (integrand D S n k z B) (Ioc 0 (2 / nu D n)) ∧
        ∫ s in Ioc 0 (2 / nu D n), integrand D S n k z B s ≤ C * rhsTested D S n k z B

/-- Alias for `BandBound` (with `rhsTested`). -/
abbrev BandBoundTested (D : SeqData) : Prop := BandBound D

/-- **Tail** `s > H = 2/ν` (source 4440-4455, `eq:short-causal-long-forward` propagation to `b`
then `eq:ct-tested-impulse`, `eq:ct-absolute-impulse` 3272-3289; above `b` the exponentially
decaying factor 4445-4446): the integrand is integrable and its integral is at most `C · rhs`. -/
def TailBound (D : SeqData) : Prop :=
  ForActual D fun S =>
    ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∀ k : ℕ, k ≤ 1 → ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ B, IsBclass D.K.as (nu D n) B →
        IntegrableOn (integrand D S n k z B) (Ioi (2 / nu D n)) ∧
        ∫ s in Ioi (2 / nu D n), integrand D S n k z B s ≤ C * rhs D S n k z B

/-- **Assembly** (source 4432-4460): band plus tail. -/
theorem laterOutputSource_of (D : SeqData) (hb : BandBound D) (ht : TailBound D) :
    LaterOutputSource D := by
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨C1, N1, _hC1, h1⟩ := hb dm dp hst κ hκ m hm S hS
  obtain ⟨C2, N2, h2⟩ := ht dm dp hst κ hκ m hm S hS
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hS
  refine ⟨max C1 C2, max N0 (max N1 N2), fun n hn k hk z hz B hB => ?_⟩
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn12 : max N1 N2 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨FI, hSn⟩ := hN0 n hn0
  obtain ⟨i1, b1⟩ := h1 n (le_trans (le_max_left _ _) hn12) k hk z hz B hB
  obtain ⟨i2, b2⟩ := h2 n (le_trans (le_max_right _ _) hn12) k hk z hz B hB
  have hpos : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have hH : (0 : ℝ) ≤ 2 / nu D n := by positivity
  have hsplit : (S n).momentC D.Pl.eigenvalue D.Pl.kappa (D.mu n z) k B =
      (∫ s in Ioc 0 (2 / nu D n), integrand D S n k z B s) +
        ∫ s in Ioi (2 / nu D n), integrand D S n k z B s := by
    have e : (S n).momentC D.Pl.eigenvalue D.Pl.kappa (D.mu n z) k B =
        ∫ s in Ioi (0 : ℝ), integrand D S n k z B s := rfl
    rw [e, ← Set.Ioc_union_Ioi_eq_Ioi hH]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi i1 i2
  have hc : 0 < (S n).c := by
    rw [hSn]
    exact cOf_pos hpos
  have hpref0 : 0 ≤ (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ * nu D n ^ (3 + 2 * D.mu n z) /
      (S n).c) * nu D n ^ k := by positivity
  have htN0 : 0 ≤ testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa (nu D n) (D.mu n z : ℂ)
      (1.1 / nu D n) ((S n).gB B) := by
    unfold testedNorm
    exact setIntegral_nonneg measurableSet_Ioc fun t ht =>
      mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (inv_nonneg.2 (norm_nonneg _)))
        (norm_nonneg _)
  have hrhsT0 : 0 ≤ rhsTested D S n k z B := by
    unfold rhsTested
    exact mul_nonneg hpref0 htN0
  have hrhs0 : 0 ≤ rhs D S n k z B := by
    unfold rhs
    positivity
  have b1' : ∫ s in Ioc 0 (2 / nu D n), integrand D S n k z B s ≤
      max C1 C2 * rhsTested D S n k z B :=
    b1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrhsT0)
  have b2' : ∫ s in Ioi (2 / nu D n), integrand D S n k z B s ≤
      max C1 C2 * rhs D S n k z B :=
    b2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hrhs0)
  rw [hsplit]
  unfold rhsTested at b1'
  unfold rhs at b2'
  refine (add_le_add b1' b2').trans (le_of_eq ?_)
  ring

end LaterOutput

end G1

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif
