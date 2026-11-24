import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_4

/-!
# Part II-b, task `PartII-b:T12/1/4/2` (`PPLExtract`): decomposition

Source of record: `the November 2 reference manuscript` lines 1933-1935 ("dividing
its `r`-th power by `N` and letting `N → ∞`; there is no period loss").

Steps: weak limit on every window along one subsequence (`PPLWeakLimit`); the limit is a.e.
`c`-periodic (`PPLShift`); window norm bound by norming (`PPLNorm`); fold to an everywhere periodic
representative (`PPLFold`); passage from the window bound to the cell average (`PPLAvg`); the planar
Helmholtz identities pass to the weak limit (`PPLHelm`) and to the representative (`PPLTransfer`).
Proved here: `pplExtract_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Common hypotheses of the extraction step. -/
def PPLCtx (r C c : ℝ) (F : ℝ × ℝ → CMerid) (H : ℕ → ℝ × ℝ → CMerid) : Prop :=
  1 < r ∧ 0 < C ∧ 0 < c ∧ CylLp c r F ∧ CylLp c 2 F ∧ PPLProps r C c F H

/-- `G` is the weak limit of `H ∘ φ` on every window `W_M`: `G ∈ L²(W_M)` and for every
`ψ ∈ L²(W_M)` the (bilinear) pairings over `W_M` converge. -/
def PPLWeak (c : ℝ) (H : ℕ → ℝ × ℝ → CMerid) (φ : ℕ → ℕ) (G : ℝ × ℝ → CMerid) : Prop :=
  (∀ M : ℕ, MemLp G 2 (volume.restrict (ppWindow c M))) ∧
    ∀ (M : ℕ) (ψ : ℝ × ℝ → CMerid), MemLp ψ 2 (volume.restrict (ppWindow c M)) →
      Tendsto (fun N => ∫ z in ppWindow c M, ∑ i : Fin 2, H (φ N) z i * ψ z i) atTop
        (𝓝 (∫ z in ppWindow c M, ∑ i : Fin 2, G z i * ψ z i))

/-- **Leaf `T12/1/4/2/1`** (weak extraction; SP 1933-1935): by `bound2`, `H_N|_{W_M}` is bounded in
the Hilbert space `L²(W_M; ℂ²)` uniformly in `N`; a diagonal subsequence over `M` has a weak limit
on every window (`Infra/WeaklyNullCompact/Extraction.lean` or
`WeakL2.exists_subseq_weakTendsto_forall`, `Analysis/WeakCompactness.lean`); limits on nested windows
are compatible by uniqueness of weak limits; glue to a function `G` on the plane. -/
def PPLWeakLimit : Prop :=
  ∀ (r C c : ℝ) (F : ℝ × ℝ → CMerid) (H : ℕ → ℝ × ℝ → CMerid), PPLCtx r C c F H →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℝ × ℝ → CMerid, PPLWeak c H φ G

/-- **Leaf `T12/1/4/2/2`** (periodicity from `almostPeriodic`): pairing `H_N(· + c) - H_N → 0` in
`L²(W_M)` with `ψ ∈ L²(W_M)` (translate of `ψ` is supported in `W_{M+1}`), pass to the limit, norm by
duality (`Lib/CZCore/Norming.lean`, `eLpNorm_le_of_forall_test_pairing_of_memLp_two` or du
Bois-Reymond): `G(· + c) = G` a.e. on `W_M`. -/
def PPLShift : Prop :=
  ∀ (r C c : ℝ) (F : ℝ × ℝ → CMerid) (H : ℕ → ℝ × ℝ → CMerid), PPLCtx r C c F H →
    ∀ (φ : ℕ → ℕ) (G : ℝ × ℝ → CMerid), StrictMono φ → PPLWeak c H φ G →
      ∀ M : ℕ, (fun z : ℝ × ℝ => G (z.1 + c, z.2)) =ᵐ[volume.restrict (ppWindow c M)] G

/-- **Leaf `T12/1/4/2/3`** (norming; `Lib/CZCore/Norming.lean:311`
`eLpNorm_le_of_forall_test_pairing_of_memLp_two`): `|∫_{W_M} G·ψ| = lim |∫_{W_M} H_{φ N}·ψ| ≤
(bound `boundR`) ‖ψ‖_{r'}`, so `‖G‖_{L^r(W_M)} ≤ C (2Mc)^{1/r} ‖F‖_{L^r(avgμ)}`. -/
def PPLNorm : Prop :=
  ∀ (r C c : ℝ) (F : ℝ × ℝ → CMerid) (H : ℕ → ℝ × ℝ → CMerid), PPLCtx r C c F H →
    ∀ (φ : ℕ → ℕ) (G : ℝ × ℝ → CMerid), StrictMono φ → PPLWeak c H φ G →
      ∀ M : ℕ, eLpNorm G (ENNReal.ofReal r) (volume.restrict (ppWindow c M)) ≤
        ENNReal.ofReal C * ENNReal.ofReal (2 * M * c) ^ (1 / r) *
          eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)

/-- **Leaf `T12/1/4/2/4`** (periodic fold, `toIcoMod`, `Short/PartII-b/Tasks/HilbertEnergy/SPeriodic.lean`):
`Gp z = G (toIcoMod hc 0 z.1, z.2)`.  If `G(z + c) = G(z)` for a.e. `z` of each window then (translates
of null sets are null, countable union over `k ∈ ℤ`) `Gp = G` a.e. on each window. -/
def PPLFold : Prop :=
  ∀ (c : ℝ) (G : ℝ × ℝ → CMerid), 0 < c →
    (∀ M : ℕ, (fun z : ℝ × ℝ => G (z.1 + c, z.2)) =ᵐ[volume.restrict (ppWindow c M)] G) →
      ∃ Gp : ℝ × ℝ → CMerid, (∀ z : ℝ × ℝ, Gp (z.1 + c, z.2) = Gp z) ∧
        ∀ M : ℕ, Gp =ᵐ[volume.restrict (ppWindow c M)] G

/-- **Leaf `T12/1/4/2/5`** (window to cell; `W_1 = [-c, c) × ℝ` is two cells, `avgμ c = c⁻¹ • cellμ c`;
by periodicity `∫_{W_1} |Gp|^r = 2 ∫_{cell} |Gp|^r`, so the `(2c)^{1/r}` cancels). -/
def PPLAvg : Prop :=
  ∀ (r C c : ℝ) (F Gp : ℝ × ℝ → CMerid), 1 < r → 0 < C → 0 < c →
    eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) < ⊤ →
    (∀ z : ℝ × ℝ, Gp (z.1 + c, z.2) = Gp z) →
    AEStronglyMeasurable Gp (volume.restrict (ppWindow c 1)) →
    eLpNorm Gp (ENNReal.ofReal r) (volume.restrict (ppWindow c 1)) ≤
      ENNReal.ofReal C * ENNReal.ofReal (2 * ((1 : ℕ) : ℝ) * c) ^ (1 / r) *
        eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) →
      MemLp Gp (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ∧
        eLpNorm Gp (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≤
          ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)

/-- **Leaf `T12/1/4/2/6`** (identities pass to the limit): `divFree` and `orth` are `lim` of the
integrals of `H_N` against compactly supported smooth tests; a test lies in `L²(W_M)` for `M` large
(compact support, smooth); `∫_ℝ² = ∫_{W_M}`; `F ∈ L²_loc` from `CylLp c 2 F` (periodic); integrability of
the pairings (`MemLp 2` on `W_M` times bounded compactly supported test); `weak limit` along `φ`
(subsequence of the convergent-to-0 sequence). -/
def PPLHelm : Prop :=
  ∀ (r C c : ℝ) (F : ℝ × ℝ → CMerid) (H : ℕ → ℝ × ℝ → CMerid), PPLCtx r C c F H →
    ∀ (φ : ℕ → ℕ) (G : ℝ × ℝ → CMerid), StrictMono φ → PPLWeak c H φ G →
      IsPlaneHelmholtz F G

/-- **Leaf `T12/1/4/2/7`** (transfer along a.e. equality on every window): `Gp = G` a.e. on the plane
(countable union of the windows, `⋃ M, W_M = univ`), so integrability and integrals of the pairings
agree. -/
def PPLTransfer : Prop :=
  ∀ (c : ℝ) (F G Gp : ℝ × ℝ → CMerid), 0 < c →
    (∀ M : ℕ, Gp =ᵐ[volume.restrict (ppWindow c M)] G) → IsPlaneHelmholtz F G →
      IsPlaneHelmholtz F Gp

theorem pplExtract_of (h1 : PPLWeakLimit) (h2 : PPLShift) (h3 : PPLNorm) (h4 : PPLFold)
    (h5 : PPLAvg) (h6 : PPLHelm) (h7 : PPLTransfer) : PPLExtract := by
  intro r hr C hC c hc F hF hF2 H hP
  have hctx : PPLCtx r C c F H := ⟨hr, hC, hc, hF, hF2, hP⟩
  obtain ⟨φ, hφ, G, hG⟩ := h1 r C c F H hctx
  have hs := h2 r C c F H hctx φ G hφ hG
  have hn := h3 r C c F H hctx φ G hφ hG
  have hh := h6 r C c F H hctx φ G hφ hG
  obtain ⟨Gp, hper, hae⟩ := h4 c G hc hs
  have hae1 := hae 1
  have hmeas : AEStronglyMeasurable Gp (volume.restrict (ppWindow c 1)) :=
    ((hG.1 1).aestronglyMeasurable).congr hae1.symm
  have hb : eLpNorm Gp (ENNReal.ofReal r) (volume.restrict (ppWindow c 1)) ≤
      ENNReal.ofReal C * ENNReal.ofReal (2 * ((1 : ℕ) : ℝ) * c) ^ (1 / r) *
        eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) :=
    (le_of_eq (eLpNorm_congr_ae hae1)).trans (hn 1)
  have hFfin : eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) < ⊤ := hF.2.eLpNorm_lt_top
  obtain ⟨hmem, hle⟩ := h5 r C c F Gp hr hC hc hFfin hper hmeas hb
  exact ⟨Gp, ⟨hper, hmem⟩, h7 c F G Gp hc hae hh, hle⟩

end UnforcedLeray.Short.IIb
