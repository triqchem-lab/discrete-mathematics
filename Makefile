AGDA = agda +RTS -M8G -H6G -A128M -RTS

# 仓库里有同名目录 `test/` ⇒ 不声明 .PHONY 时 make 会判定目标"已是最新"而空跑
.PHONY: test

# 2026-10-26 修：原清单有 28 条指向重组前的旧布局（Sovereign/<Area> →
# Sovereign/{Algebra,Synthesis,Application}/<Area>），已按 basename 逐一重映射
# （46 条全部存在且唯一）。
test:
	$(AGDA) src/Sovereign/Algebra/FieldTower/TriCycGraph.agda
	$(AGDA) src/Sovereign/Synthesis/Combinatorics/ArthurMagicSquare.agda
	$(AGDA) src/Sovereign/Synthesis/Physics/MotorStableStates.agda
	$(AGDA) src/Sovereign/Application/Physics/QuantumMotor.agda
	$(AGDA) src/Sovereign/Algebra/FieldTower/TriadicHarmonic.agda
	$(AGDA) src/Sovereign/Algebra/NumberTheory/DigitalRootCycle.agda
	$(AGDA) src/Sovereign/Algebra/GroupTheory/C3Orbit.agda
	$(AGDA) src/Sovereign/Application/Geometry/ProjectiveCore.agda
	$(AGDA) src/Sovereign/Application/Geometry/ProjectiveOrbit.agda
	$(AGDA) src/Sovereign/Application/Geometry/ProjectiveInvariants.agda
	$(AGDA) src/Sovereign/Application/Geometry/ProjectiveTransform.agda
	$(AGDA) src/Sovereign/Application/Geometry/ConformalCore.agda
	$(AGDA) src/Sovereign/Application/Geometry/ConformalInvariants.agda
	$(AGDA) src/Sovereign/Application/Geometry/TorusGeometry.agda
	$(AGDA) src/Sovereign/Application/Geometry/TorusGeodesic.agda
	$(AGDA) src/Sovereign/Application/Geometry/TorusAlgebra.agda
	$(AGDA) src/Sovereign/Application/Geometry/TorusFourier.agda
	$(AGDA) src/Sovereign/Synthesis/Combinatorics/GF4AffineMagicSquare.agda
	$(AGDA) src/Sovereign/Synthesis/Combinatorics/GF9AffineMagicSquare.agda
	$(AGDA) src/Sovereign/Synthesis/Combinatorics/DynamicMagicSquare.agda
	$(AGDA) src/Sovereign/Synthesis/Representation/SL23Cayley.agda
	$(AGDA) src/Sovereign/Synthesis/A4/BinaryTetrahedralIrreducibility.agda
	$(AGDA) src/Sovereign/Application/Physics/DiscreteStatMech.agda
	$(AGDA) src/Sovereign/Synthesis/Format/Positional.agda
	$(AGDA) src/Sovereign/Synthesis/Format/Doz.agda
	$(AGDA) src/Sovereign/Synthesis/NumberTheory/DigitField.agda
	$(AGDA) src/Sovereign/Synthesis/NumberTheory/DigitRealization.agda
	$(AGDA) src/Sovereign/Application/Problems/ABC/ABCL1.agda
	$(AGDA) src/Sovereign/Algebra/GF9FrobeniusC4.agda
	$(AGDA) src/Sovereign/Algebra/GroupTheory/BraidGroup.agda
	$(AGDA) src/Sovereign/Algebra/GroupTheory/Word.agda
	$(AGDA) src/Sovereign/Algebra/GroupTheory/BraidCongruence.agda
	$(AGDA) src/Sovereign/Algebra/GroupTheory/BraidToSL23.agda
	$(AGDA) src/Sovereign/Algebra/GroupTheory/BraidQuotient.agda
	$(AGDA) src/Sovereign/Algebra/LinearAlgebra/Matrix2Laws.agda
	$(AGDA) src/Sovereign/Synthesis/Representation/Fin3Semiring.agda
	$(AGDA) src/Sovereign/Synthesis/Representation/Matrix2Inverse.agda
	$(AGDA) src/Sovereign/Synthesis/Representation/Matrix2DetMul.agda
	$(AGDA) src/Sovereign/Synthesis/Representation/SL2SetoidGroup.agda
	$(AGDA) src/Sovereign/Synthesis/Representation/SetoidFreeGroupUniversal.agda
	$(AGDA) src/Sovereign/Synthesis/Representation/SL2Bridge.agda
	$(AGDA) src/Sovereign/Synthesis/Representation/BraidGroupSetoid.agda
	$(AGDA) src/Sovereign/Synthesis/Representation/BraidQuotientRec.agda
	$(AGDA) src/Sovereign/Synthesis/Representation/BraidQuotientCubical.agda
	$(AGDA) src/Sovereign/Synthesis/Representation/BraidQuotientCubicalEval.agda
	$(AGDA) src/Sovereign/Synthesis/Representation/BraidQuotientCubicalGroup.agda
	@echo "ALL_PASS"
