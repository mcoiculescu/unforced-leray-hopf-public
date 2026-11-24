import UnforcedLeray.Short.PartIIIb.Concrete.SourceL

/-!
# Decomposition of `sourceLAmbient` (source 4917-4937, kernel facts 4870-4900)

Source: `the November 2 reference manuscript`.

`sourceLAmbient_of` reduces `SourceLAmbient` to
* `LptScale`: `Lpt` at general `ε` is `ε³` times `Lpt` at `ε = 1`;
* `JetEps1`: the `ε = 1` jet bound `|(s∂_s)^j 𝓛M(s)| ≤ C s^{5/2} N₀(M)`, `j ≤ 6`.
`jetEps1_of` reduces `JetEps1` to
* `NewtonVRegionBound`: smoothness and decay of the zero-width Newton field `V` on `|w|² > ν`;
* `StreamCutJet`: the outward stream cutoff of any field with that decay has the same jet bound.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Euclidean length squared. -/
def eucSq (w : Vec3) : ℝ := ∑ i, w i ^ 2

/-- Exact scaling (source 4783-4796): `𝓛` at `ε` is `ε³` times `𝓛` at `ε = 1`
(`Xmt_ε(y) = ε² Xmt_1(εy)`, `chiYr ν ε χy r = chiYr ν 1 χy (ε r)`, `Ψ` scales by `ε⁰`). -/
def LptScale : Prop :=
  ∀ (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3), 0 < ε → ∀ s : ℝ,
    Lpt c ν ε μ χo χy M s = ε ^ 3 • Lpt c ν 1 μ χo χy M s

/-- The `ε = 1` jet bound (source 4917-4937): `|(s∂_s)^j 𝓛M(s)| ≤ C s^{5/2} N₀(M)` for `j ≤ 6`,
uniformly in `c, ν ≤ 1, μ ∈ K`. -/
def JetEps1 (K : Set ℝ) (χo χy : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ (c ν μ : ℝ), LHyp c ν 1 μ χo χy → μ ∈ K →
    ∀ M : Chart → Mat3, OldThinFinite c ν M → ∀ s : ℝ, 0 < s → ∀ j : ℕ, j ≤ 6 →
      frob (sDerivIter j (Lpt c ν 1 μ χo χy M) s) ≤ C * s ^ (5 / 2 : ℝ) * oldN0 c ν M

/-- The zero-width Newton field on the receiver region (source 4776-4782, 4870-4900): for old thin
`M` with finite `N₀`, `V_{μ,M}` is `C^7` on `{|w|² > ν}` with
`‖∂^m V(w)‖ ≤ C_m N₀(M) |w|^{-4-m}` (`D³N` has `|∂^m D³N(z)| ≤ C_m |z|^{-4-m}`, `|z| ≥ c|w|`
since the source `x'` has `|x'|² < 5ν/6`, `∫|Σ_M| ≤ π N₀`, `t^{2μ+2} ≤ 1`). -/
def NewtonVRegionBound (χo : ℝ → ℝ) : Prop :=
  ∃ C : ℕ → ℝ, ∀ (c ν μ : ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo → 0 ≤ μ →
    ∀ M : Chart → Mat3, OldThinFinite c ν M →
      ContDiffOn ℝ 7 (newtonV c ν μ χo M) {w | ν * (11 / 12) < eucSq w} ∧
      ∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
        ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M) w‖ ≤ C m * oldN0 c ν M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)

/-- The stream cutoff (source 4178-4186, 4917-4937: "the same separated-kernel bounds, on the
outward primitive ray, control the stream cutoff and its fixed conormal derivatives"): if a field
`Z` is `C^7` on `{|w|² > 11ν/12}` with `‖∂^m Z(w)‖ ≤ B |w|^{-4-m}` for `m ≤ 7`, then
`X = 𝒞_y Z` (with `ε = 1`) is differentiable at every receiver `(s^{-1/2},0,0)` and the matrix
`s ↦ D X(s^{-1/2},0,0)` has `|(s∂_s)^j ·| ≤ C₀ B s^{5/2}` for `j ≤ 6`, with `C₀` depending only on
`χ̂_y` (`ν/r² ≤ 1` on the support of `χ_y`, `(r∂_r)^j χ̂_y(ν/r²)` bounded, `Ψ_Z = O(B r^{-2})`,
each fixed `r∂_r` costs `r^{-5}`; `X = 0` near `r² ≤ ν`). -/
def StreamCutJet (χy : ℝ → ℝ) : Prop :=
  ∃ C0 : ℝ, ∀ (ν B : ℝ), 0 < ν → 0 ≤ B → ∀ Z : Vec3 → Vec3,
    ContDiffOn ℝ 7 Z {w | ν * (11 / 12) < eucSq w} →
    (∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
      ‖iteratedFDeriv ℝ m Z w‖ ≤ B * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) →
    IsStreamCutoff χy →
    ∀ s : ℝ, 0 < s → ∀ j : ℕ, j ≤ 6 →
      frob (sDerivIter j (fun s : ℝ => if 0 < s then
        (fun i j => fderiv ℝ (streamCut ν 1 χy Z) ![(1 : ℝ)⁻¹ / Real.sqrt s, 0, 0] (Pi.single j 1) i)
        else (0 : Mat3)) s) ≤ C0 * B * s ^ (5 / 2 : ℝ)

theorem jetEps1_of {K : Set ℝ} {χo χy : ℝ → ℝ} (hV : NewtonVRegionBound χo)
    (hS : StreamCutJet χy) : JetEps1 K χo χy := by
  obtain ⟨C, hC⟩ := hV
  obtain ⟨C0, hC0⟩ := hS
  refine ⟨C0 * ∑ m ∈ Finset.range 8, (|C m| + |C m|), ?_⟩
  intro c ν μ h _ M hM s hs j hj
  have hN0 := oldN0_nonneg c ν h.nu_pos M
  have hmu0 : 0 ≤ μ := h.mu_pos.le
  have hmu1 : 0 ≤ μ + 1 := by linarith
  obtain ⟨h1, h1b⟩ := hC c ν μ h.c_pos h.nu_pos h.chiO hmu0 M hM
  obtain ⟨h2, h2b⟩ := hC c ν (μ + 1) h.c_pos h.nu_pos h.chiO hmu1 M hM
  have hY : ∀ μ' : ℝ, youngW c ν 1 μ' χo M = newtonV c ν μ' χo M := by
    intro μ'; funext y; simp [youngW]
  set S : ℝ := ∑ m ∈ Finset.range 8, (|C m| + |C m|) with hSdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun m _ => by positivity
  set Z : Vec3 → Vec3 := newtonV c ν μ χo M - newtonV c ν (μ + 1) χo M with hZ
  have hopen : IsOpen {w : Vec3 | ν * (11 / 12) < eucSq w} := by
    unfold eucSq
    exact isOpen_lt continuous_const (by fun_prop)
  have hZs : ContDiffOn ℝ 7 Z {w | ν * (11 / 12) < eucSq w} := h1.sub h2
  have hZb : ∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
      ‖iteratedFDeriv ℝ m Z w‖ ≤ (S * oldN0 c ν M) * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by
    intro m hm w hw
    have hat1 : ContDiffAt ℝ 7 (newtonV c ν μ χo M) w := h1.contDiffAt (hopen.mem_nhds hw)
    have hat2 : ContDiffAt ℝ 7 (newtonV c ν (μ + 1) χo M) w := h2.contDiffAt (hopen.mem_nhds hw)
    have hmle : (m : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hm
    rw [hZ, iteratedFDeriv_sub_apply (hat1.of_le hmle) (hat2.of_le hmle)]
    have hp : 0 ≤ (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hb1 := h1b m hm w hw
    have hb2 := h2b m hm w hw
    have hSm : |C m| + |C m| ≤ S :=
      Finset.single_le_sum (f := fun m => |C m| + |C m|) (fun m _ => by positivity)
        (Finset.mem_range.2 (by omega))
    have hCm : C m + C m ≤ S := le_trans (add_le_add (le_abs_self _) (le_abs_self _)) hSm
    calc ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M) w - iteratedFDeriv ℝ m (newtonV c ν (μ + 1) χo M) w‖
        ≤ ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M) w‖ + ‖iteratedFDeriv ℝ m (newtonV c ν (μ + 1) χo M) w‖ :=
          norm_sub_le _ _
      _ ≤ C m * oldN0 c ν M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) +
          C m * oldN0 c ν M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := add_le_add hb1 hb2
      _ = (C m + C m) * (oldN0 c ν M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) := by ring
      _ ≤ S * (oldN0 c ν M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) :=
          mul_le_mul_of_nonneg_right hCm (mul_nonneg hN0 hp)
      _ = (S * oldN0 c ν M) * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by ring
  have hL : Lpt c ν 1 μ χo χy M = fun s : ℝ => if 0 < s then
        (fun i j => fderiv ℝ (streamCut ν 1 χy Z) ![(1 : ℝ)⁻¹ / Real.sqrt s, 0, 0] (Pi.single j 1) i)
        else (0 : Mat3) := by
    funext s'
    simp only [Lpt, Xmt, hY, hZ]
  rw [hL]
  have := hC0 ν (S * oldN0 c ν M) h.nu_pos (mul_nonneg hSnn hN0) Z hZs hZb h.chiY s hs j hj
  calc _ ≤ C0 * (S * oldN0 c ν M) * s ^ (5 / 2 : ℝ) := this
    _ = C0 * S * s ^ (5 / 2 : ℝ) * oldN0 c ν M := by ring

theorem sourceLAmbient_of {as : ℝ} {K : Set ℝ} {χo χy : ℝ → ℝ} (hS : LptScale)
    (hJ : JetEps1 K χo χy) : SourceLAmbient as K χo χy := by
  intro has _ _
  obtain ⟨C, hC⟩ := hJ
  refine ⟨7 * |C|, ?_⟩
  intro c ν ε μ h hμ M hM s hs
  have hε := h.eps_pos
  have hN0 := oldN0_nonneg c ν h.nu_pos M
  have hL : Lpt c ν ε μ χo χy M = ε ^ 3 • Lpt c ν 1 μ χo χy M := funext fun s' => hS c ν ε μ χo χy M hε s'
  have hit : ∀ j : ℕ, sDerivIter j (ε ^ 3 • Lpt c ν 1 μ χo χy M) = ε ^ 3 • sDerivIter j (Lpt c ν 1 μ χo χy M) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      funext t
      simp only [sDerivIter, sDeriv, ih]
      rw [show (ε ^ 3 • sDerivIter j (Lpt c ν 1 μ χo χy M)) = fun t => ε ^ 3 • sDerivIter j (Lpt c ν 1 μ χo χy M) t from rfl,
        deriv_fun_const_smul_field (ε ^ 3)]
      simp only [Pi.smul_apply]
      exact smul_comm _ _ _
  have hj : ∀ j ∈ Finset.range 7, frob (sDerivIter j (Lpt c ν ε μ χo χy M) s) ≤
      ε ^ 3 * (|C| * s ^ (5 / 2 : ℝ) * oldN0 c ν M) := by
    intro j hj'
    rw [hL, hit j]
    have h1 := hC c ν μ (LHyp.mk h.c_pos h.nu_pos h.nu_le one_pos h.mu_pos h.mu_lt h.chiO h.chiY) hμ M hM s hs j (by simpa [Nat.lt_succ_iff] using hj')
    have hfs : frob (ε ^ 3 • sDerivIter j (Lpt c ν 1 μ χo χy M) s) =
        ε ^ 3 * frob (sDerivIter j (Lpt c ν 1 μ χo χy M) s) := by
      unfold frob
      have : ∀ i k, (ε ^ 3 • sDerivIter j (Lpt c ν 1 μ χo χy M) s) i k ^ 2 =
          (ε ^ 3) ^ 2 * (sDerivIter j (Lpt c ν 1 μ χo χy M) s i k) ^ 2 := by
        intro i k; simp [mul_pow]
      simp only [this, ← Finset.mul_sum]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    show frob (ε ^ 3 • sDerivIter j (Lpt c ν 1 μ χo χy M) s) ≤ _
    rw [hfs]
    have hpos : 0 ≤ ε ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_left (le_trans h1 (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hs.le _)) hN0)) hpos
  unfold affTerm affSum
  have hsum := Finset.sum_le_sum hj
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hsp : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have hex : Real.exp (-as * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hsm : s ^ (-(5 / 2 : ℝ)) * s ^ (5 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hs]; simp
  have hs0 : 0 ≤ s ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have hnn : 0 ≤ ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (Lpt c ν ε μ χo χy M) s) :=
    Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _
  calc Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) * ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (Lpt c ν ε μ χo χy M) s)
      ≤ 1 * s ^ (-(5 / 2 : ℝ)) * ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (Lpt c ν ε μ χo χy M) s) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hex hs0) hnn
    _ ≤ 1 * s ^ (-(5 / 2 : ℝ)) * ((7 : ℕ) * (ε ^ 3 * (|C| * s ^ (5 / 2 : ℝ) * oldN0 c ν M))) :=
        mul_le_mul_of_nonneg_left (by simpa using hsum) (by positivity)
    _ = 7 * |C| * ε ^ 3 * oldN0 c ν M * (s ^ (-(5 / 2 : ℝ)) * s ^ (5 / 2 : ℝ)) := by push_cast; ring
    _ = 7 * |C| * ε ^ 3 * oldN0 c ν M := by rw [hsm, mul_one]

end UnforcedLeray.Short.PartIIIb.Concrete
