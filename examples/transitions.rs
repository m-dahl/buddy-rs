use buddy_rs::*;

fn main() {
    let bdd = take_manager(1000, 1000, 4);
    let x0 = bdd.ithvar(0);
    let x1 = bdd.ithvar(2);
    let x2 = bdd.ithvar(1);
    let x3 = bdd.ithvar(3);

    let nx0 = bdd.nithvar(0);
    let nx1 = bdd.nithvar(2);
    let nx2 = bdd.nithvar(1);
    let nx3 = bdd.nithvar(3);

    let normvars = &[ 0, 2 ];
    let primvars = &[ 1, 3 ];

    let normset = bdd.make_set(normvars);

    let pair = &[ (1, 0), (3, 2) ];
    let pair = bdd.make_pair(pair);

    let guard = bdd.and(&nx0, &nx1);
    let action = bdd.and(&x2, &bdd.biimp(&x1, &x3)); // keep value
    let trans = bdd.and(&guard, &action);

    let guard1 = bdd.and(&nx0, &nx1);
    let action1 = bdd.and(&x3, &bdd.biimp(&x0, &x2));
    let trans1 = bdd.and(&guard1, &action1);

    let initial = bdd.and(&nx0, &nx1);

    let fw = bdd.or(&trans, &trans1);

    let mut r = initial.clone();
    loop {
        let old = r;
        let new = bdd.relprod(&old, &fw, &normset);
        let new = bdd.replace(&new, &pair);
        r = bdd.or(&old, &new);

        if old == r {
            break;
        }
    }

    println!("reachable states: {}", bdd.satcount(&r) / f64::powf(2.0, primvars.len() as f64));

    bdd.allsat(&r, |s| {
        println!("satisfying: {:?}", s);
    });

    let support = bdd.support(&r);
    let support_vars = bdd.scan_set(&support);
    println!("supported by: {:?}", support_vars);

    let stats = bdd.get_stats();
    println!("{:#?}", stats);
    return_manager(bdd);
}
