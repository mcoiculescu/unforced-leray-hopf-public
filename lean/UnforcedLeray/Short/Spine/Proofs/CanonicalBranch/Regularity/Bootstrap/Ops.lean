import UnforcedLeray.Short.Spine.Sub.SP_CAN4

/-!
# Spine: operator facts for the time bootstrap (helper of `Regularity/Bootstrap.lean`)

Source of record: `the November 2 reference manuscript` line 1086 and 1141-1145;
target `StrongBootstrap` (`Short/Spine/Sub/SP_CAN4.lean`).

Facts about the spectral powers `(I - D)^s` on `XG`:
* `(I - D)^{-s}` (`s ≥ 0`) is a bounded operator `Pneg s`, of norm at most one, whose range is the
  domain `X_{G,j}` of `(I - D)^{s}`, with `(I - D)^{s} (I - D)^{-s} = 1` and the reverse;
* `L₀` acts on `X_{G,j}` through a bounded operator `M_j` on `XG`: `(I - D)^{j/2} L₀ f = M_j
  ((I - D)^{j/2} f)` (`exists_M`). This is the form the time bootstrap differentiates.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.Spine.BootOps

open UnforcedLeray.B0010 UnforcedLeray.B0123 UnforcedLeray.B0094

theorem norm_idMult_neg_le {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : ‖idMult (-s) n‖ ≤ 1 := by
  rw [norm_idMult]
  refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
  · have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  · linarith

theorem idMult_zero (n : ℕ) : idMult 0 n = 1 := by
  simp [idMult]

theorem idMult_neg_mul (s : ℝ) (n : ℕ) : idMult (-s) n * idMult s n = 1 := by
  have h := congrFun (idMult_mul (-s) s) n
  rw [Pi.mul_apply, neg_add_cancel] at h
  rw [h, idMult_zero]

theorem norm_idMult_mul_neg (s : ℝ) (n : ℕ) : ‖idMult s n‖ * ‖idMult (-s) n‖ = 1 := by
  rw [← norm_mul, mul_comm, idMult_neg_mul, norm_one]

/-- Equal vectors give equal `(I - D)^s` values, whatever the domain proofs. -/
theorem IDpow_congr_val {s : ℝ} {x y : XG} (hx : x ∈ (IDpow s).domain)
    (hy : y ∈ (IDpow s).domain) (h : x = y) : IDpow s ⟨x, hx⟩ = IDpow s ⟨y, hy⟩ := by
  subst h
  rfl

/-- `(I - D)^{-s}` is total for `s ≥ 0`. -/
theorem mem_domain_neg (s : ℝ) (hs : 0 ≤ s) (g : XG) : g ∈ (IDpow (-s)).domain :=
  mem_mulOp_domain_of_bdd oscBasis (idMult (-s)) (norm_idMult_neg_le hs) g

/-- The bounded operator `(I - D)^{-s}` on `XG`, `s ≥ 0`. -/
def Pneg (s : ℝ) (hs : 0 ≤ s) : XG →L[ℂ] XG :=
  diagCLM oscBasis (idMult (-s)) 1 (norm_idMult_neg_le hs)

theorem Pneg_apply (s : ℝ) (hs : 0 ≤ s) (g : XG) :
    Pneg s hs g = IDpow (-s) ⟨g, mem_domain_neg s hs g⟩ :=
  (mulOp_eq_diagCLM oscBasis (idMult (-s)) (norm_idMult_neg_le hs) g).symm

theorem norm_Pneg_le (s : ℝ) (hs : 0 ≤ s) (g : XG) : ‖Pneg s hs g‖ ≤ ‖g‖ := by
  have h1 := hasSum_norm_mulOp_sq oscBasis (idMult (-s)) ⟨g, mem_domain_neg s hs g⟩
  have h2 := hasSum_norm_inner_sq oscBasis g
  have hle : ‖IDpow (-s) ⟨g, mem_domain_neg s hs g⟩‖ ^ 2 ≤ ‖g‖ ^ 2 := by
    refine hasSum_le (fun n => ?_) h1 h2
    have hn := norm_idMult_neg_le hs n
    have h0 : 0 ≤ ‖idMult (-s) n‖ := norm_nonneg _
    have hp : ‖idMult (-s) n‖ ^ 2 ≤ 1 := pow_le_one₀ h0 hn
    have hq : 0 ≤ ‖⟪oscBasis n, g⟫_ℂ‖ ^ 2 := by positivity
    nlinarith
  rw [Pneg_apply]
  nlinarith [norm_nonneg (IDpow (-s) ⟨g, mem_domain_neg s hs g⟩), norm_nonneg g]

/-- `(I - D)^{s} (I - D)^{-s}` is the identity on `XG`: its range lies in `X_{G,j}`. -/
theorem mem_domain_of_neg (s : ℝ) (hs : 0 ≤ s) (g : XG) : Pneg s hs g ∈ (IDpow s).domain := by
  rw [Pneg_apply]
  refine (mem_mulOp_domain_iff_summable oscBasis (idMult s) _).2 ?_
  have key : ∀ n : ℕ, ‖idMult s n‖ ^ 2 * ‖⟪oscBasis n, IDpow (-s) ⟨g, mem_domain_neg s hs g⟩⟫_ℂ‖ ^ 2
      = ‖⟪oscBasis n, g⟫_ℂ‖ ^ 2 := by
    intro n
    have hc : ⟪oscBasis n, IDpow (-s) ⟨g, mem_domain_neg s hs g⟩⟫_ℂ
        = idMult (-s) n * ⟪oscBasis n, g⟫_ℂ :=
      inner_IDpow (-s) ⟨g, mem_domain_neg s hs g⟩ n
    rw [hc, norm_mul]
    calc ‖idMult s n‖ ^ 2 * (‖idMult (-s) n‖ * ‖⟪oscBasis n, g⟫_ℂ‖) ^ 2
        = (‖idMult s n‖ * ‖idMult (-s) n‖) ^ 2 * ‖⟪oscBasis n, g⟫_ℂ‖ ^ 2 := by ring
      _ = ‖⟪oscBasis n, g⟫_ℂ‖ ^ 2 := by rw [norm_idMult_mul_neg, one_pow, one_mul]
  exact (hasSum_norm_inner_sq oscBasis g).summable.congr (fun n => (key n).symm)

/-- `(I - D)^{-s}` followed by `(I - D)^{s}` is the identity. -/
theorem IDpow_pos_neg (s : ℝ) (hs : 0 ≤ s) (g : XG) :
    IDpow s ⟨Pneg s hs g, mem_domain_of_neg s hs g⟩ = g := by
  apply ext_inner_basis oscBasis
  intro n
  rw [inner_IDpow]
  dsimp only
  rw [Pneg_apply, inner_IDpow, ← mul_assoc, mul_comm (idMult s n) (idMult (-s) n),
    idMult_neg_mul, one_mul]

/-- `(I - D)^{-s} ((I - D)^{s} f) = f` for `f ∈ X_{G,j}`. -/
theorem Pneg_IDpow (s : ℝ) (hs : 0 ≤ s) (f : XG) (hf : f ∈ (IDpow s).domain) :
    Pneg s hs (IDpow s ⟨f, hf⟩) = f := by
  rw [Pneg_apply]
  apply ext_inner_basis oscBasis
  intro n
  rw [inner_IDpow]
  dsimp only
  rw [inner_IDpow, ← mul_assoc, idMult_neg_mul, one_mul]

/-- The `X_{G,j}` bound of `L₀`, with the squared graph norm written as `xgjNorm`. -/
theorem L0_bound (j : ℕ) (hE : B0122.GreenEllipticRegularity j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : XG, ∀ hf : f ∈ XGj j,
      ∃ hL : B0012.L0 f ∈ XGj j, xgjNorm j ⟨B0012.L0 f, hL⟩ ≤ C * xgjNorm j ⟨f, hf⟩ := by
  obtain ⟨C, hC, h⟩ := B0122.L0_mem_XGj_norm j hE
  refine ⟨C, hC, fun f hf => ?_⟩
  obtain ⟨hL, hb⟩ := h f ((XGj_eq_B0121 j).le hf)
  refine ⟨(XGj_eq_B0121 j).ge hL, ?_⟩
  have e1 : Real.sqrt (B0121.graphNormSq j ⟨B0012.L0 f, hL⟩)
      = xgjNorm j ⟨B0012.L0 f, (XGj_eq_B0121 j).ge hL⟩ := by
    rw [graphNormSq_eq_xgjNorm_sq]
    exact Real.sqrt_sq (xgjNorm_nonneg _ _)
  have e2 : Real.sqrt (B0121.graphNormSq j ⟨f, (XGj_eq_B0121 j).le hf⟩)
      = xgjNorm j ⟨f, hf⟩ := by
    rw [graphNormSq_eq_xgjNorm_sq]
    exact Real.sqrt_sq (xgjNorm_nonneg _ _)
  rw [e1, e2] at hb
  exact hb

/-- `‖(I - D)^{s} y‖ ≤ ‖y‖_{X_{G,j}}` (graph norm). -/
theorem norm_IDpow_le_xgjNorm (j : ℕ) (y : XG) (hy : y ∈ XGj j) :
    ‖IDpow ((j : ℝ) / 2) ⟨y, hy⟩‖ ≤ xgjNorm j ⟨y, hy⟩ := by
  have h := Real.abs_le_sqrt (x := ‖IDpow ((j : ℝ) / 2) ⟨y, hy⟩‖)
    (y := ‖y‖ ^ 2 + ‖IDpow ((j : ℝ) / 2) ⟨y, hy⟩‖ ^ 2) (by nlinarith [sq_nonneg ‖y‖])
  rw [abs_norm] at h
  exact h

/-- The bounded operator `M_j` representing `L₀` on `X_{G,j}`:
`(I - D)^{j/2} L₀ f = M_j ((I - D)^{j/2} f)` for `f ∈ X_{G,j}`. -/
theorem exists_M (j : ℕ) (hE : B0122.GreenEllipticRegularity j) :
    ∃ M : XG →L[ℂ] XG, ∀ f : XG, ∀ hf : f ∈ XGj j, ∃ hL : B0012.L0 f ∈ XGj j,
      IDpow ((j : ℝ) / 2) ⟨B0012.L0 f, hL⟩ = M (IDpow ((j : ℝ) / 2) ⟨f, hf⟩) := by
  obtain ⟨C, hC, hL⟩ := L0_bound j hE
  have hs : (0 : ℝ) ≤ (j : ℝ) / 2 := by positivity
  have hPmem : ∀ g : XG, Pneg ((j : ℝ) / 2) hs g ∈ XGj j :=
    fun g => mem_domain_of_neg ((j : ℝ) / 2) hs g
  have hLmem : ∀ g : XG, B0012.L0 (Pneg ((j : ℝ) / 2) hs g) ∈ XGj j := by
    intro g
    obtain ⟨h, -⟩ := hL (Pneg ((j : ℝ) / 2) hs g) (hPmem g)
    exact h
  let Q : XG →ₗ[ℂ] XGj j :=
    LinearMap.codRestrict (XGj j)
      (((B0012.L0 : XG →L[ℂ] XG) : XG →ₗ[ℂ] XG).comp
        ((Pneg ((j : ℝ) / 2) hs : XG →L[ℂ] XG) : XG →ₗ[ℂ] XG)) hLmem
  let Lin : XG →ₗ[ℂ] XG := (IDpow ((j : ℝ) / 2)).toFun.comp Q
  have hbd : ∀ g : XG, ‖Lin g‖ ≤ (2 * C) * ‖g‖ := by
    intro g
    obtain ⟨hLg, hb⟩ := hL (Pneg ((j : ℝ) / 2) hs g) (hPmem g)
    have h1 : ‖Lin g‖ ≤ xgjNorm j ⟨B0012.L0 (Pneg ((j : ℝ) / 2) hs g), hLmem g⟩ :=
      norm_IDpow_le_xgjNorm j _ _
    have h2 : xgjNorm j ⟨Pneg ((j : ℝ) / 2) hs g, hPmem g⟩ ≤ 2 * ‖g‖ := by
      unfold xgjNorm
      have hp := norm_Pneg_le ((j : ℝ) / 2) hs g
      have hq : IDpow ((j : ℝ) / 2) ⟨Pneg ((j : ℝ) / 2) hs g, hPmem g⟩ = g :=
        IDpow_pos_neg ((j : ℝ) / 2) hs g
      rw [hq]
      apply Real.sqrt_le_iff.2
      refine ⟨by positivity, ?_⟩
      have hn : 0 ≤ ‖g‖ := norm_nonneg g
      have hp0 : 0 ≤ ‖Pneg ((j : ℝ) / 2) hs g‖ := norm_nonneg _
      nlinarith
    calc ‖Lin g‖ ≤ xgjNorm j ⟨B0012.L0 (Pneg ((j : ℝ) / 2) hs g), hLmem g⟩ := h1
      _ ≤ C * xgjNorm j ⟨Pneg ((j : ℝ) / 2) hs g, hPmem g⟩ := hb
      _ ≤ C * (2 * ‖g‖) := mul_le_mul_of_nonneg_left h2 hC
      _ = (2 * C) * ‖g‖ := by ring
  refine ⟨LinearMap.mkContinuous Lin (2 * C) hbd, fun f hf => ?_⟩
  obtain ⟨hLf, -⟩ := hL f hf
  refine ⟨hLf, ?_⟩
  have hPinv : Pneg ((j : ℝ) / 2) hs (IDpow ((j : ℝ) / 2) ⟨f, hf⟩) = f :=
    Pneg_IDpow ((j : ℝ) / 2) hs f hf
  have hM : (LinearMap.mkContinuous Lin (2 * C) hbd) (IDpow ((j : ℝ) / 2) ⟨f, hf⟩)
      = IDpow ((j : ℝ) / 2) ⟨B0012.L0 (Pneg ((j : ℝ) / 2) hs (IDpow ((j : ℝ) / 2) ⟨f, hf⟩)),
          hLmem _⟩ := rfl
  rw [hM]
  exact IDpow_congr_val _ _ (congrArg B0012.L0 hPinv).symm

end UnforcedLeray.Short.Spine.BootOps
