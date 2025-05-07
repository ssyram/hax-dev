mod my_mod {
    pub fn index(index: usize, values: &[u8]) -> u8 {
        values[index]
    }
}

fn my_main() {
    let values = [1u8, 2, 3];
    my_mod::index(1, &values);
}

fn main() {}

fn pattern_matching() -> u8 {
    match 1 {
        1 => 1 + 1,
        _ => 1 - 1,
    }
}

fn generic<A, const N: usize>(x: A) -> A {
    if N > 1 {
        x
    } else {
        x
    }
}

fn generic_call() {
    generic::<usize, 3>(1);
}
