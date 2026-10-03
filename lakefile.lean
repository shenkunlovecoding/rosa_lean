import Lake
open Lake DSL

package leanFormalization

/-- The whole run-compressed ROSA formalization.  Std-only (no Mathlib). -/
@[default_target]
lean_lib LeanFormalization where
  srcDir := "."
  roots := #[`Route, `CutArith, `HookCut, `QCut, `Lcs, `RunRectangle, `Repair,
             `Capacity, `RunRectangleLcp, `RunHookSummary, `AffineEnvelope,
             `OwnerEnvelope, `RosBridge, `CommonBirth, `QBridge, `Interior, `RspSummary,
             `KDeleteAbstract, `KSkyline, `KDeleteROSA, `OwnerBridges, `OwnerCompress,
             `OwnerCorrect, `OwnerCorrectK, `WinnerPieces, `Gluing, `Phase12b,
             `KSuffix, `HookDegenerate, `BoundaryPartition, `CapacityComplete,
             `AffineLifetime, `KDeleteEquivalence, `BlockWinnerNoReentry,
             `BoundaryRangeCount, `PayloadContraction, `CapacityMultiRun,
             `BoundaryCertificates, `BridgeEnvelope, `HookScan,
             `BoundaryZeroCertificates, `PayloadRouteAdapter,
             `RunHookCompressedScan, `BoundaryRecursive,
             `OwnerTemplateEquivalence, `CapacityConcrete, `RunHookCoverage,
             `BoundaryRunExtractor, `OwnerKBaselineEnvelope,
             `CapacityRunDecomposition, `BoundaryOptionalWindow,
             `OwnerKWindowDischarge, `CapacityAutomaticRunCover,
             `EnvelopeEssentialEvents, `EnvelopeExecutable,
             `EffectiveOwnerM3, `RunRectangleInitial,
             `PayloadErrorBound, `CreditRepairReduce, `CreditQEExpiry,
             `CreditBlockConv, `CreditCRT, `CreditCandidateCount, `Check]
