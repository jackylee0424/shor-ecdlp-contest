#!/usr/bin/env python3
"""Reproduce the shipped Entrant's declared bounds from source formulas.

Bench reference: 535a493. All costs are the challenge's abstract T model.
Default stdout is the two requested integers; --details shows the derivation.
Sources and distinctions between bounds and exact costs: docs/BASELINE-BREAKDOWN.md.
This calculator reads no bench files and does not elaborate or expand circuits.
"""
import argparse


def breakdown():
    n, phase, point = 257, 265, 513
    # Arithmetic/{Adder,RippleAdder,ModAdd,ModSub}.lean, *_tCount.
    full_adder = 3 * 7
    ripple = n * full_adder
    mod_compute = 2 * ripple
    mod_add = 2 * mod_compute + 7 * n
    # InPlaceAdder/InPlaceModular: Cuccaro, reduction, controlled addition.
    inplace_add = 2 * 7 * n
    reduction = inplace_add + 2 * 7 * n + inplace_add
    modular_double = reduction  # shifts and the final CX are free
    controlled_mod_add = 112 * n
    # LowSpaceModMul.horner_tCount/program_tCount; Secp256k1Instance.mulCost.
    mul = n * (modular_double + controlled_mod_add)
    # Secp256k1Instance.secpCost: 2n-1 multiplications, n word selects,
    # followed by the reverse computation. This is a generic exponent schedule.
    exponent_forward = (2 * n - 1) * mul + 7 * n * n
    exponent = 2 * exponent_forward
    # PointAdd field wrappers copy into the engine, copy out, and reverse it.
    field_add = field_sub = 2 * mod_add
    field_mul, field_inv = 2 * mul, 2 * exponent
    # PointAdd.genericPointCompute and doublePointCompute include local reversals.
    generic = 9 * field_sub + 4 * field_mul + 2 * field_inv
    three_x_squared = 2 * field_mul + 3 * field_add
    doubling = (2 * three_x_squared + 7 * field_add
                + 4 * field_mul + 2 * field_inv)
    # Two 256-bit equality flags and three CCX conjunctions.
    flags = 2 * (14 * (256 - 1)) + 3 * 7
    controlled_copy = 7 * point
    generic_branch = 2 * generic + controlled_copy
    double_branch = 2 * doubling + controlled_copy
    infinity_branch = controlled_copy
    finite_compute = flags + generic_branch + double_branch + infinity_branch
    point_add_out = 2 * finite_compute
    controlled_out = 2 * (finite_compute + controlled_copy)
    controlled_point = 2 * controlled_out  # forward C, swap, reverse -C
    qft = 15 * phase * (phase - 1) // 2
    scalar_axis = phase * controlled_point
    total_t = 2 * scalar_axis + 2 * qft

    # Secp256k1Instance.historyCount n = 3n-1 (n>0).
    history = 3 * n - 1
    # Register IDs: 0..3 public/initial, 4..773 history, 774 duplicate,
    # 775 modulus, 776 mask, then one-bit flags at IDs 777, 778, 779.
    exponent_full_blocks = 4 + history + 1 + 2
    exponent_sparse = exponent_full_blocks * n + 3
    engine_dense = (exponent_full_blocks + 3) * n
    point_local = (7 * n + 256 + 1 + 4 * 256 + 6 + 2 * point)
    controlled_work = 2 * point  # temporary output and choice registers
    total_q = 2 * phase + point + 1 + controlled_work + point_local + engine_dense
    # All add/mul engine ports are within the first full exponent blocks.
    sparse_layout_q = total_q - engine_dense + exponent_sparse
    rows = {
        'full adder (one bit)': full_adder,
        'ripple adder (257 bits)': ripple,
        'modular add/sub compute': mod_compute,
        'clean modular add/sub': mod_add,
        'in-place add/sub': inplace_add,
        'modular reduction/doubling': reduction,
        'controlled modular add': controlled_mod_add,
        'Horner multiply': mul,
        'modular exponentiation/Fermat engine': exponent,
        'field add/sub wrapper': field_add,
        'field multiply wrapper': field_mul,
        'field inversion wrapper': field_inv,
        'generic affine coordinate computation': generic,
        '3*x^2 computation': three_x_squared,
        'doubling coordinate computation': doubling,
        'point flags/setup': flags,
        'generic branch (compute/copy/reverse)': generic_branch,
        'doubling branch (compute/copy/reverse)': double_branch,
        'infinity branch': infinity_branch,
        'finite point computation': finite_compute,
        'point add out-of-place': point_add_out,
        'controlled point add out-of-place': controlled_out,
        'controlled point add in-place': controlled_point,
        'one 265-step scalar axis': scalar_axis,
        'one 265-bit inverse QFT': qft,
    }
    # Independently published intermediate equalities catch formula transcription errors.
    assert mod_add == 23387
    assert mul == 10171546
    assert exponent == 10436930882
    assert generic == 41829516862 and doubling == 41911076326
    assert finite_compute == 167481204310
    assert controlled_point == 669924831604
    assert history == 770 and point_local == 4112
    assert total_q == 206642
    assert total_t == 355060161799520
    # Non-overlapping leaf attribution used in the report.
    assert controlled_point == (176 * field_add + 96 * field_mul
                                 + 32 * field_inv + 4 * flags + 16 * controlled_copy)
    # Check sparse engine union directly from the concrete register block IDs.
    def block(index):
        return set(range(index * n, (index + 1) * n))
    exponent_wires = set(range(exponent_full_blocks * n))
    exponent_wires.update(index * n for index in range(777, 780))
    adder_wires = set().union(*(block(index) for index in (0, 1, 2, 3, 4, 5, 7, 9)))
    adder_wires.update((6 * n, 8 * n))
    multiplier_wires = set().union(*(block(index) for index in range(5)))
    multiplier_wires.update((5 * n, 6 * n, 7 * n))
    assert len(adder_wires) == 8 * n + 2
    assert len(multiplier_wires) == 5 * n + 3
    assert adder_wires | multiplier_wires <= exponent_wires
    assert len(exponent_wires) == exponent_sparse
    # Cross-check the distinct 26-trial Naive numeric certificate.
    naive_qft = 15 * 256 * 255 // 2
    assert 26 * (512 * controlled_point + 2 * naive_qft) == 8918039383771648
    return total_q, total_t, rows, {
        'phase registers': 2 * phase,
        'point register': point,
        'shared QFT ancilla': 1,
        'controlled-point temporary/choice': controlled_work,
        'point local workspace': point_local,
        'dense arithmetic-engine envelope': engine_dense,
        'isolated modular-adder layout': 8 * n + 2,
        'isolated Horner multiplier layout': 5 * n + 3,
        'Fermat history registers alone (included above)': history * n,
        'sparse engine layout cardinality': exponent_sparse,
        'sparse whole-layout upper bound (not a new Lean certificate)': sparse_layout_q,
        'dense envelope slack': engine_dense - exponent_sparse,
        'measurements': 2 * phase,
        'coefficient rows': 2 * phase,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--details', action='store_true')
    args = parser.parse_args()
    qubits, t_model, costs, wires = breakdown()
    if args.details:
        for label, value in costs.items():
            print(f'{label}: {value:,} T')
        print()
        for label, value in wires.items():
            print(f'{label}: {value:,}')
        print('\nDeclared qubits and T model:')
    print(qubits)
    print(t_model)


if __name__ == '__main__':
    main()
