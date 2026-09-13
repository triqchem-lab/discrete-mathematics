AGDA = agda +RTS -M8G -H6G -A128M -RTS

test:
	$(AGDA) src/Sovereign/Algebra/TriCycGraph.agda
	$(AGDA) src/Sovereign/Structology/ArthurMagicSquare.agda
	$(AGDA) src/Sovereign/Structology/MotorStableStates.agda
	$(AGDA) src/Sovereign/Physics/QuantumMotor.agda
	$(AGDA) src/Sovereign/Algebra/TriadicHarmonic.agda
	$(AGDA) src/Sovereign/Algebra/DigitalRootCycle.agda
	$(AGDA) src/Sovereign/Algebra/C3Orbit.agda
	$(AGDA) src/Sovereign/Geometry/ProjectiveCore.agda
	$(AGDA) src/Sovereign/Geometry/ProjectiveOrbit.agda
	$(AGDA) src/Sovereign/Geometry/ProjectiveInvariants.agda
	$(AGDA) src/Sovereign/Geometry/ProjectiveTransform.agda
	$(AGDA) src/Sovereign/Geometry/ConformalCore.agda
	$(AGDA) src/Sovereign/Geometry/ConformalInvariants.agda
	$(AGDA) src/Sovereign/Geometry/TorusGeometry.agda
	$(AGDA) src/Sovereign/Geometry/TorusGeodesic.agda
	$(AGDA) src/Sovereign/Geometry/TorusAlgebra.agda
	$(AGDA) src/Sovereign/Geometry/TorusFourier.agda
	$(AGDA) src/Sovereign/Structology/GF4AffineMagicSquare.agda
	$(AGDA) src/Sovereign/Structology/GF9AffineMagicSquare.agda
	$(AGDA) src/Sovereign/Structology/DynamicMagicSquare.agda
	$(AGDA) src/Sovereign/Structology/SL23Cayley.agda
	$(AGDA) src/Sovereign/Structology/BinaryTetrahedralIrreducibility.agda
	$(AGDA) src/Sovereign/Physics/DiscreteStatMech.agda
	$(AGDA) src/Sovereign/Format/Positional.agda
	$(AGDA) src/Sovereign/Format/Doz.agda
	$(AGDA) src/Sovereign/Format/DigitField.agda
	$(AGDA) src/Sovereign/Format/DigitRealization.agda
	$(AGDA) src/Sovereign/Problem/ABC/ABCL1.agda
	@echo "ALL_PASS"
