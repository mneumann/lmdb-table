extern crate lmdb_rs as lmdb;

use lmdb::{FromMdbValue, ToMdbValue};
use lmdb::core::{MdbResult, Transaction};
use std::marker::PhantomData;

pub trait Tablename {
    fn as_str() -> &'static str;
}

pub trait IsNativeInt {}
impl IsNativeInt for i32 {}
impl IsNativeInt for u32 {}
impl IsNativeInt for i64 {}
impl IsNativeInt for u64 {}

/// A table that maps an integer to a set of integers.
/// Keys K1 and K2 must be native integers!
#[derive(Clone)]
pub struct IntToIntsTable<K1, K2, T> {
    pub db: lmdb::DbHandle,
    _k1: PhantomData<K1>,
    _k2: PhantomData<K2>,
    _t: PhantomData<T>,
}

/// A table that maps an integer to a blob.
#[derive(Clone)]
pub struct IntToBlobTable<K, T> {
    pub db: lmdb::DbHandle,
    _k: PhantomData<K>,
    _t: PhantomData<T>,
}

/// A table that maps an object of type `K` to a blob.
#[derive(Clone)]
pub struct KeyToBlobTable<K, T> {
    pub db: lmdb::DbHandle,
    _k: PhantomData<K>,
    _t: PhantomData<T>,
}

/// A table that maps an integer to a record/struct.
#[derive(Clone)]
pub struct IntToRecordTable<K, V, T> {
    pub db: lmdb::DbHandle,
    _k: PhantomData<K>,
    _v: PhantomData<V>,
    _t: PhantomData<T>,
}

/// Bound IntToRecordTable. 
pub struct BoundIntToRecordTable<'a, K, V, T> {
    db: lmdb::Database<'a>,
    _k: PhantomData<K>,
    _v: PhantomData<V>,
    _t: PhantomData<T>,
}

/* Implementations */

impl<K1, K2, T> IntToIntsTable<K1, K2, T>
where K1: Sized + ToMdbValue + IsNativeInt + FromMdbValue,
      K2: Sized + ToMdbValue + IsNativeInt,
      T: Tablename
{
    fn flags() -> lmdb::core::DbFlags {
        lmdb::core::DbIntKey |
        lmdb::core::DbAllowDups | lmdb::core::DbAllowIntDups |
        lmdb::core::DbDupFixed
    }

    pub fn create(env: &lmdb::Environment) -> IntToIntsTable<K1, K2, T> {
        IntToIntsTable::new_from_handle(env.create_db(T::as_str(), Self::flags()).unwrap())
    }

    pub fn open(env: &lmdb::Environment) -> IntToIntsTable<K1, K2, T> {
        IntToIntsTable::new_from_handle(env.get_db(T::as_str(), Self::flags()).unwrap())
    }

    fn new_from_handle(db: lmdb::DbHandle) -> IntToIntsTable<K1, K2, T> {
        IntToIntsTable {db: db, _k1: PhantomData, _k2: PhantomData, _t: PhantomData}
    }

    // XXX: Can we optimize this, when iter is already sorted for example?
    pub fn insert_multiple<I>(&self, txn: &Transaction, iter: I) -> MdbResult<()> where I: Iterator<Item=(K1,K2)> {
        let db = txn.bind(&self.db);
        for (ref k1, ref k2) in iter {
            try!(db.set(k1, k2));
        }
        Ok(())
    }

    pub fn insert(&self, txn: &Transaction, kv: &(K1, K2)) -> MdbResult<()> {
        let db = txn.bind(&self.db);
        db.set(&kv.0, &kv.1)
    }

    fn last_key(&self, txn: &lmdb::core::ReadonlyTransaction) -> MdbResult<K1> {
        let db = txn.bind(&self.db);
        let mut cursor = try!(db.new_cursor());
        try!(cursor.to_last());
        cursor.get_key()
    }
}


impl<K, T> IntToBlobTable<K, T>
where K: Sized + ToMdbValue + IsNativeInt,
      T: Tablename
{
    fn flags() -> lmdb::core::DbFlags {
        lmdb::core::DbIntKey
    }

    pub fn create(env: &lmdb::Environment) -> IntToBlobTable<K, T> {
        IntToBlobTable::new_from_handle(env.create_db(T::as_str(), Self::flags()).unwrap())
    }

    pub fn open(env: &lmdb::Environment) -> IntToBlobTable<K, T> {
        IntToBlobTable::new_from_handle(env.get_db(T::as_str(), Self::flags()).unwrap())
    }

    fn new_from_handle(db: lmdb::DbHandle) -> IntToBlobTable<K, T> {
        IntToBlobTable {db: db, _k: PhantomData, _t: PhantomData}
    }

    pub fn insert(&self, txn: &Transaction, key: &K, val: &[u8]) -> MdbResult<()> {
        let db = txn.bind(&self.db);
        db.insert(key, &val)
    }

    // fn lookup
}


impl<K, T> KeyToBlobTable<K, T>
where K: Sized + ToMdbValue,
      T: Tablename
{
    fn flags() -> lmdb::core::DbFlags {
        lmdb::core::DbFlags::empty()
    }

    pub fn create(env: &lmdb::Environment) -> KeyToBlobTable<K, T> {
        KeyToBlobTable::new_from_handle(env.create_db(T::as_str(), Self::flags()).unwrap())
    }

    pub fn open(env: &lmdb::Environment) -> KeyToBlobTable<K, T> {
        KeyToBlobTable::new_from_handle(env.get_db(T::as_str(), Self::flags()).unwrap())
    }

    fn new_from_handle(db: lmdb::DbHandle) -> KeyToBlobTable<K, T> {
        KeyToBlobTable {db: db, _k: PhantomData, _t: PhantomData}
    }

    pub fn insert(&self, txn: &Transaction, key: &K, val: &[u8]) -> MdbResult<()> {
        let db = txn.bind(&self.db);
        db.insert(key, &val)
    }

    // fn lookup
}

//
// A unique(native-int) -> sized record value lookup table
//

impl<K, V, T> IntToRecordTable<K, V, T>
where K: Sized + ToMdbValue + IsNativeInt,
      V: Sized + ToMdbValue + FromMdbValue,
      T: Tablename
{
    fn flags() -> lmdb::core::DbFlags {
        lmdb::core::DbIntKey
    }

    pub fn create(env: &lmdb::Environment) -> IntToRecordTable<K, V, T> {
        IntToRecordTable::new_from_handle(env.create_db(T::as_str(), Self::flags()).unwrap())
    }

    pub fn open(env: &lmdb::Environment) -> IntToRecordTable<K, V, T> {
        IntToRecordTable::new_from_handle(env.get_db(T::as_str(), Self::flags()).unwrap())
    }

    fn new_from_handle(db: lmdb::DbHandle) -> IntToRecordTable<K, V, T> {
        IntToRecordTable {db: db, _k: PhantomData, _v: PhantomData, _t: PhantomData}
    }

    pub fn bind_to_txn<'a>(&self, txn: &'a lmdb::Transaction) -> BoundIntToRecordTable<'a, K, V, T> {
        BoundIntToRecordTable {
            db: txn.bind(&self.db),
            _k: PhantomData, _v: PhantomData, _t: PhantomData}
    }

    pub fn bind_to_ro_txn<'a>(&self, txn: &'a lmdb::ReadonlyTransaction) -> BoundIntToRecordTable<'a, K, V, T> {
        BoundIntToRecordTable {
            db: txn.bind(&self.db),
            _k: PhantomData, _v: PhantomData, _t: PhantomData}
    }
}

impl<'a, K, V, T> BoundIntToRecordTable<'a, K, V, T>
where K: Sized + ToMdbValue + IsNativeInt,
      V: Sized + ToMdbValue + FromMdbValue,
      T: Tablename
{
    // fails if key exists.
    pub fn insert(&self, key: &K, val: &V) -> MdbResult<()> {
        self.db.insert(key, val)
    }

    // XXX: Should go into ReadonlyBound...
    pub fn lookup(&self, key: &K) -> MdbResult<V> {
        self.db.get::<V>(key)
    }

    pub fn update<F>(&self, key: &K, update: F) -> MdbResult<()>
        where F: Fn(&mut V) -> bool {

        let mut cursor = try!(self.db.new_cursor());
        try!(cursor.to_key(key));

        let mut value: V = try!(cursor.get_value());

        let needs_update = update(&mut value);

        if needs_update {
            try!(cursor.replace(&value));
        }

        Ok(())
    }

    pub fn insert_or_update<N, F>(&self, key: &K, insert_fn: N, update_fn: F) -> MdbResult<()>
        where
                N: Fn() -> V,
                F: Fn(&mut V) -> bool {

        // Trying to update first
        {
                let mut cursor = try!(self.db.new_cursor());
                if let Ok(_) = cursor.to_key(key) {
                        let mut value: V = try!(cursor.get_value());
                        let needs_update = update_fn(&mut value);
                        if needs_update {
                                try!(cursor.replace(&value));
                        }
                        return Ok(());
                }
        }

        // Now try to insert
        {
            let value: V = insert_fn();
            try!(self.db.insert(key, &value));
            return Ok(());
        }
    }

    pub fn insert_or_update_default<F>(&self, key: &K, update_fn: F) -> MdbResult<bool>
        where
                V: Default,
                F: Fn(&mut V) -> bool {

        // Trying to update first
        {
                let mut cursor = try!(self.db.new_cursor());
                if let Ok(_) = cursor.to_key(key) {
                        let mut value: V = try!(cursor.get_value());
                        let needs_update = update_fn(&mut value);
                        if needs_update {
                                try!(cursor.replace(&value));
                        }
                        return Ok(needs_update);
                }
        }

        // Now try to insert
        {
            let mut value: V = V::default();
            let needs_update = update_fn(&mut value);
            if needs_update {
                try!(self.db.insert(key, &value));
            }
            return Ok(needs_update);
        }
    }
}
