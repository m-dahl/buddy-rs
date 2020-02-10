use buddy_sys;

pub type BDDVar = i32;

#[derive(Debug, PartialEq)]
pub struct BDD {
    root: buddy_sys::BDD
}

#[derive(Debug, PartialEq)]
pub struct BDDStats {
    /// Total number of new nodes ever produced.
    pub produced: i64,
    /// Currently allocated number of bdd nodes.
    pub node_num: i32,
    /// User defined maximum number of bdd nodes.
    pub max_node_num: i32,
    /// Number of currently free nodes.
    pub free_nodes: i32,
    /// Minimum number of nodes that should be left after a garbage collection.
    pub min_free_nodes: i32,
    /// Number of defined bdd variables.
    pub var_num: i32,
    /// Number of entries in the internal caches.
    pub cache_size: i32,
    /// Number of garbage collections done until now.
    pub gbc_num: i32,
}

#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Clone)]
pub enum Valuation {
    False,
    True,
    DontCare,
}

pub struct BDDManager(*mut i32); // mut pointer to prevent send

pub struct BDDPair {
    ptr: *mut buddy_sys::s_bddPair
}

impl Drop for BDDPair {
    fn drop(&mut self) {
        unsafe { buddy_sys::bdd_freepair(self.ptr); }
    }
}

impl BDDManager {
    pub fn set_varnum(&self, n: i32) {
        unsafe { buddy_sys::bdd_setvarnum(n) };
    }
    pub fn ext_varnum(&self, n: i32) {
        unsafe { buddy_sys::bdd_extvarnum(n) };
    }
    pub fn get_varnum(&self) -> i32 {
        unsafe { buddy_sys::bdd_varnum() }
    }

    pub fn get_stats(&self) -> BDDStats {
        let mut c_stats = buddy_sys::s_bddStat {
            produced: 0,
            nodenum: 0,
            maxnodenum: 0,
            freenodes: 0,
            minfreenodes: 0,
            varnum: 0,
            cachesize: 0,
            gbcnum: 0
        };

        unsafe { buddy_sys::bdd_stats(&mut c_stats) };
        BDDStats {
            produced: c_stats.produced,
            node_num: c_stats.nodenum,
            max_node_num: c_stats.maxnodenum,
            free_nodes: c_stats.freenodes,
            min_free_nodes: c_stats.minfreenodes,
            var_num: c_stats.varnum,
            cache_size: c_stats.cachesize,
            gbc_num: c_stats.gbcnum,
        }
    }

    pub fn make_pair(&self, pairs: &[(BDDVar, BDDVar)]) -> BDDPair {
        let c_pair = unsafe { buddy_sys::bdd_newpair() };

        for (oldvar, newvar) in pairs {
            unsafe { buddy_sys::bdd_setpair(c_pair, *oldvar, *newvar); }
        }
        BDDPair { ptr: c_pair }
    }

    pub fn ithvar(&self, n: BDDVar) -> BDD {
        // does not need to be reference counted
        let r = unsafe { buddy_sys::bdd_ithvar(n) };
        BDD {
            root: r
        }
    }

    pub fn nithvar(&self, n: BDDVar) -> BDD {
        // does not need to be reference counted
        let r = unsafe { buddy_sys::bdd_nithvar(n) };
        BDD {
            root: r
        }
    }

    pub fn one(&self) -> BDD {
        BDD { root : unsafe { buddy_sys::bddtrue } }
    }

    pub fn zero(&self) -> BDD {
        BDD { root: unsafe { buddy_sys::bddfalse } }
    }

    pub fn satcount(&self, f: &BDD) -> f64 {
        unsafe { buddy_sys::bdd_satcount(f.root) }
    }

    pub fn satcount_set(&self, f: &BDD, set: &BDD) -> f64 {
        unsafe { buddy_sys::bdd_satcountset(f.root, set.root) }
    }

    // BDD operations
    pub fn not(&self, a: &BDD) -> BDD {
        let bdd = unsafe { buddy_sys::bdd_not(a.root) };
        BDD::from(bdd)
    }

    pub fn and(&self, a: &BDD, b: &BDD) -> BDD {
        let bdd = unsafe { buddy_sys::bdd_apply(a.root, b.root,
                                                buddy_sys::bddop_and)
        };
        BDD::from(bdd)
    }

    pub fn or(&self, a: &BDD, b: &BDD) -> BDD {
        let bdd = unsafe { buddy_sys::bdd_apply(a.root, b.root,
                                                buddy_sys::bddop_or) };
        BDD::from(bdd)
    }

    pub fn xor(&self, a: &BDD, b: &BDD) -> BDD {
        let bdd = unsafe { buddy_sys::bdd_apply(a.root, b.root,
                                                buddy_sys::bddop_xor) };
        BDD::from(bdd)
    }

    pub fn imp(&self, a: &BDD, b: &BDD) -> BDD {
        let bdd = unsafe { buddy_sys::bdd_apply(a.root, b.root,
                                                buddy_sys::bddop_imp) };
        BDD::from(bdd)
    }

    pub fn biimp(&self, a: &BDD, b: &BDD) -> BDD {
        let bdd = unsafe { buddy_sys::bdd_apply(a.root, b.root,
                                                buddy_sys::bddop_biimp) };
        BDD::from(bdd)
    }

    pub fn relprod(&self, a: &BDD, b: &BDD, vars: &BDD) -> BDD {
        let bdd = unsafe { buddy_sys::bdd_appex(a.root,b.root,
                                                buddy_sys::bddop_and,
                                                vars.root) };
        BDD::from(bdd)
    }

    pub fn replace(&self, a: &BDD, pair: &BDDPair) -> BDD {
        let bdd = unsafe { buddy_sys::bdd_replace(a.root, pair.ptr) };
        BDD::from(bdd)
    }

    pub fn support(&self, f: &BDD) -> BDD {
        let bdd = unsafe { buddy_sys::bdd_support(f.root) };
        BDD::from(bdd)
    }

    pub fn constrain(&self, f: &BDD, c: &BDD) -> BDD {
        let bdd = unsafe { buddy_sys::bdd_constrain(f.root, c.root) };
        BDD::from(bdd)
    }

    pub fn simplify(&self, f: &BDD, d: &BDD) -> BDD {
        let bdd = unsafe { buddy_sys::bdd_simplify(f.root, d.root) };
        BDD::from(bdd)
    }

    pub fn exist(&self, f: &BDD, vars: &BDD) -> BDD {
        let bdd = unsafe { buddy_sys::bdd_exist(f.root, vars.root) };
        BDD::from(bdd)
    }

    pub fn allsat<T: 'static + FnMut(&[Valuation]) -> ()>(&self, f: &BDD, mut cb: T) {
        // hacks to get buddy call our function
        use std::cell::Cell;
        use std::process;

        thread_local! {
            static CTX: Cell<*mut dyn FnMut(&[Valuation])> = Cell::new(&mut |_| {
                println!("C function spawned a thread or stored a function pointer");
                process::abort();
            });
        }
        unsafe extern "C" fn wrapper(arg1: *mut ::std::os::raw::c_char, arg2: ::std::os::raw::c_int) {
            let mut vals = Vec::new();
            for i in 0..arg2 {
                let val = match *arg1.offset(i as isize) {
                    0 => Valuation::False,
                    1 => Valuation::True,
                    _ => Valuation::DontCare,
                };
                vals.push(val);
            }
            CTX.with(|ptr| (*ptr.get())(&vals))
        }
        CTX.with(move |ptr| {
            let old = ptr.get();
            ptr.set(&mut cb);
            unsafe { buddy_sys::bdd_allsat(f.root, Some(wrapper)) };
            ptr.set(old);
        });
    }

    pub fn allsat_vec(&self, f: &BDD) -> Vec<Vec<Valuation>> {
        // hacks to get around borrow checker...
        use std::cell::RefCell;
        use std::rc::Rc;
        let rf: Rc<RefCell<Vec<Vec<Valuation>>>> = Rc::new(RefCell::new(Vec::new()));
        let rfclone = rf.clone();

        self.allsat(f, move |a: &[Valuation]| {
            let mut v = rfclone.borrow_mut();
            v.push(a.to_vec());
        });

        let inner = Rc::try_unwrap(rf).unwrap();
        inner.into_inner()
    }

    pub fn scan_set(&self, set: &BDD) -> Vec<BDDVar> {
        let mut ptr: *mut i32 = std::ptr::null_mut();
        let mut len: i32 = 0;
        unsafe { buddy_sys::bdd_scanset(set.root, &mut ptr, &mut len) };
        let slice = unsafe { std::slice::from_raw_parts(ptr, len as usize) };
        Vec::from(slice)
    }

    pub fn make_set(&self, set: &[BDDVar]) -> BDD {
        let mut copy: Vec<_> = set.to_vec();
        let bdd = unsafe { buddy_sys::bdd_makeset(copy.as_mut_ptr(), set.len() as i32) };
        BDD::from(bdd)
    }

}

struct BDDOwner {
    manager: Option<BDDManager>,
}

impl BDDOwner {
    fn take_manager(&mut self, node_size: i32, cache_size: i32) -> BDDManager {
        let bdd = self.manager.take().expect(
            "Trying to use buddy in two places at the same time!");

        unsafe { buddy_sys::bdd_init(node_size,cache_size); }
        bdd
    }

    fn return_manager(&mut self, token: BDDManager) {
        unsafe { buddy_sys::bdd_done(); }
        self.manager = Some(token);
    }
}

static mut BDD_OWNER: BDDOwner = BDDOwner {
    manager: Some(BDDManager(std::ptr::null_mut())),
};


pub fn take_manager(node_size: i32, cache_size: i32) -> BDDManager {
    unsafe { BDD_OWNER.take_manager(node_size, cache_size) }
}

pub fn return_manager(manager: BDDManager) {
    unsafe { BDD_OWNER.return_manager(manager); }
}

impl Clone for BDD {
    fn clone(&self) -> Self {
        BDD::from(self.root)
    }
}

impl BDD {
    fn from(root: buddy_sys::BDD) -> Self {
        unsafe { buddy_sys::bdd_addref(root); }
        BDD {
            root
        }
    }

    pub fn low(&self) -> BDD {
        let bdd = unsafe { buddy_sys::bdd_low(self.root) };
        BDD::from(bdd)
    }

    pub fn high(&self) -> BDD {
        let bdd = unsafe { buddy_sys::bdd_high(self.root) };
        BDD::from(bdd)
    }

    pub fn var(&self) -> BDDVar {
        unsafe { buddy_sys::bdd_var(self.root) }
    }

}


impl Drop for BDD {
    fn drop(&mut self) {
        unsafe { buddy_sys::bdd_delref(self.root); }
    }
}

///
/// Note that due to the thread-unsafety of buddy, all tests need to
/// be run with --test-threads=1 to work properly!
///
/// The failing tests will make our manager "owner" crash, which may
/// cause otherwise successful tests to fail.
///

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let bdd = take_manager(1000, 1000);
        bdd.set_varnum(2);
        let a = bdd.ithvar(0);
        let b = bdd.one();
        let c = bdd.and(&a, &b);
        let d = c.clone();
        assert_eq!(b, bdd.not(&bdd.zero()));
        assert_eq!(c, d);
        assert_eq!(bdd.satcount(&c), 2.0);
        return_manager(bdd);
    }

    #[test]
    fn stats() {
        let bdd = take_manager(1000, 1000);
        bdd.set_varnum(2);
        let a = bdd.ithvar(0);
        let b = bdd.one();
        let _c = bdd.and(&a, &b);

        let stats = bdd.get_stats();
        assert_eq!(stats.var_num, 2);
        return_manager(bdd);
    }

    #[test]
    fn satcount() {
        let bdd = take_manager(1000, 1000);
        bdd.set_varnum(3);
        let a = bdd.ithvar(0);
        let b = bdd.ithvar(1);
        let c = bdd.ithvar(2);

        let ab = bdd.and(&a, &b);
        let abc = bdd.or(&ab, &c);

        let bc = bdd.and(&b, &c);

        let count = bdd.satcount(&bdd.one());
        assert_eq!(count, (1 << 3) as f64);

        let count = bdd.satcount(&bdd.zero());
        assert_eq!(count, 0.0);

        let count = bdd.satcount(&abc);
        assert_eq!(count, 5.0);

        bdd.set_varnum(4);
        let d = bdd.ithvar(3);

        let nd = bdd.not(&d);
        let abc_nd = bdd.and(&abc, &nd);

        let count = bdd.satcount(&abc_nd);
        assert_eq!(count, 5.0);

        let count = bdd.satcount(&abc);
        assert_eq!(count, 10.0);

        let count = bdd.satcount(&bc);
        assert_eq!(count, 4.0);

        return_manager(bdd);
    }

    #[test]
    fn sets() {
        let bdd = take_manager(1000, 1000);
        bdd.set_varnum(4);

        let set = bdd.make_set(&[1, 3]);

        let set_v = bdd.scan_set(&set);
        assert!(!set_v.contains(&0));
        assert!(set_v.contains(&1));
        assert!(!set_v.contains(&2));
        assert!(set_v.contains(&3));
        assert!(!set_v.contains(&4));

        return_manager(bdd);
    }

    #[test]
    fn support() {
        // this test exposes a bug in the original buddy,
        // where support crashes after reinitialization.

        let bdd = take_manager(1000, 1000);
        bdd.set_varnum(3);
        let a = bdd.ithvar(0);
        let b = bdd.ithvar(1);
        let c = bdd.ithvar(2);

        let ab = bdd.and(&a, &b);
        let abc = bdd.or(&ab, &c);

        let s = bdd.support(&abc);
        let _set = bdd.scan_set(&s);

        return_manager(bdd);

        let bdd = take_manager(1000, 1000);
        bdd.set_varnum(3);
        let a = bdd.ithvar(0);
        let b = bdd.ithvar(1);
        let c = bdd.ithvar(2);

        let ab = bdd.and(&a, &b);
        let abc = bdd.or(&ab, &c);

        let s = bdd.support(&abc);
        let _set = bdd.scan_set(&s);

        return_manager(bdd);
    }

    #[test]
    fn swap() {
        let bdd = take_manager(1000, 1000);
        bdd.set_varnum(2);
        let a = bdd.ithvar(0);
        let nb = bdd.nithvar(1);

        let anb = bdd.and(&a,&nb);

        let s = bdd.allsat_vec(&anb);
        assert_eq!(s, vec![vec![Valuation::True, Valuation::False]]);

        let pair = bdd.make_pair(&[(1,0),(0,1)]);
        let nab = bdd.replace(&anb, &pair);

        let s = bdd.allsat_vec(&nab);
        assert_eq!(s, vec![vec![Valuation::False, Valuation::True]]);

        // obvious api error here. TODO
        drop(pair);

        return_manager(bdd);
    }


    #[test]
    fn allsat() {
        let bdd = take_manager(1000, 1000);
        bdd.set_varnum(3);
        let a = bdd.ithvar(0);
        let b = bdd.ithvar(1);
        let c = bdd.ithvar(2);

        let ab = bdd.and(&a, &b);
        let abc = bdd.or(&ab, &c);

        let vn = bdd.get_varnum();
        bdd.allsat(&abc, move |a: &[Valuation]| {
            // all cubes contains all variables
            assert_eq!(a.len() as i32, vn);
        });

        return_manager(bdd);
    }

    #[test]
    fn allsat_vec() {
        let bdd = take_manager(1000, 1000);
        bdd.set_varnum(3);
        let a = bdd.ithvar(0);
        let b = bdd.ithvar(1);
        let c = bdd.ithvar(2);

        let ab = bdd.and(&a, &b);
        let abc = bdd.or(&ab, &c);

        let v = bdd.allsat_vec(&abc);

        assert_eq!(v.len(), 3); // three set of satisfying assignments.

        return_manager(bdd);
    }

    #[test]
    fn threading_is_fine() {
        let bdd = take_manager(1000, 1000);
        bdd.set_varnum(2);
        let a = bdd.ithvar(0);
        let b = bdd.one();
        let c = bdd.and(&a, &b);
        assert_eq!(bdd.satcount(&c), 2.0);
        return_manager(bdd);

        let t2 = std::thread::spawn(|| {
            // do it all again in this thread.
            let bdd = take_manager(1000, 1000);
            bdd.set_varnum(2);
            let a = bdd.ithvar(0);
            let b = bdd.one();
            let c = bdd.and(&a, &b);
            assert_eq!(bdd.satcount(&c), 2.0);
            return_manager(bdd);
        });

        let _r = t2.join();
    }


    #[test]
    fn take_manager_twice_should_panic() {
        let bdd = take_manager(1000, 1000);

        let result = std::panic::catch_unwind(|| {
            let _bdd = take_manager(1000, 1000);
        });
        assert!(result.is_err());

        return_manager(bdd);
    }


    #[test]
    fn threading_mistake_should_panic() {
        let bdd = take_manager(1000, 1000);

        // we forgot this...
        // return_manager(bdd);
        let t1 = std::thread::spawn(|| {
            // then we panic here
            let result = std::panic::catch_unwind(|| {
                let _bdd = take_manager(1000, 1000);
            });
            assert!(result.is_err());
        });

        let _r = t1.join();
        return_manager(bdd);
    }
}
