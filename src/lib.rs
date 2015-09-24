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

/// Bound IntToBlobTable. 
pub struct BoundIntToBlobTable<'a, K, T> {
    db: lmdb::Database<'a>,
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

/// A table that maps a a blob to an object of type `V`.
#[derive(Clone)]
pub struct BlobToRecordTable<V, T> {
    pub db: lmdb::DbHandle,
    _v: PhantomData<V>,
    _t: PhantomData<T>,
}

/// Bound BlobToRecordTable. 
pub struct BoundBlobToRecordTable<'a, V, T> {
    db: lmdb::Database<'a>,
    _v: PhantomData<V>,
    _t: PhantomData<T>,
}

/// A table that represenents a set of object of `K`.
#[derive(Clone)]
pub struct KeyOnlyTable<K, T> {
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

/// A table that maps an object of type `K` to a record/struct.
#[derive(Clone)]
pub struct KeyToRecordTable<K, V, T> {
    pub db: lmdb::DbHandle,
    _k: PhantomData<K>,
    _v: PhantomData<V>,
    _t: PhantomData<T>,
}

/// Bound KeyToRecordTable. 
pub struct BoundKeyToRecordTable<'a, K, V, T> {
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
    #[inline]
    pub fn insert_multiple<I>(&self, txn: &Transaction, iter: I) -> MdbResult<()> where I: Iterator<Item=(K1,K2)> {
        let db = txn.bind(&self.db);
        for (ref k1, ref k2) in iter {
            try!(db.set(k1, k2));
        }
        Ok(())
    }

    #[inline]
    pub fn insert(&self, txn: &Transaction, kv: &(K1, K2)) -> MdbResult<()> {
        let db = txn.bind(&self.db);
        db.set(&kv.0, &kv.1)
    }

/*
    fn last_key(&self, txn: &lmdb::core::ReadonlyTransaction) -> MdbResult<K1> {
        let db = txn.bind(&self.db);
        let mut cursor = try!(db.new_cursor());
        try!(cursor.to_last());
        cursor.get_key()
    }
*/
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

    #[inline]
    pub fn insert(&self, txn: &Transaction, key: &K, val: &[u8]) -> MdbResult<()> {
        let db = txn.bind(&self.db);
        db.insert(key, &val)
    }

    #[inline]
    pub fn bind_to_ro_txn<'a>(&self, txn: &'a lmdb::ReadonlyTransaction) -> BoundIntToBlobTable<'a, K, T> {
        BoundIntToBlobTable {
            db: txn.bind(&self.db),
            _k: PhantomData, _t: PhantomData}
    }
}

impl<'a, K, T> BoundIntToBlobTable<'a, K, T>
where K: Sized + ToMdbValue + IsNativeInt,
      T: Tablename
{
    // XXX: Should go into ReadonlyBound...
    #[inline]
    pub fn lookup(&self, key: &K) -> MdbResult<&'a [u8]> {
        self.db.get(key)
    }
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

    #[inline]
    pub fn insert(&self, txn: &Transaction, key: &K, val: &[u8]) -> MdbResult<()> {
        let db = txn.bind(&self.db);
        db.insert(key, &val)
    }

    // fn lookup
}

impl<V, T> BlobToRecordTable<V, T>
where V: Sized + ToMdbValue,
      T: Tablename
{
    fn flags() -> lmdb::core::DbFlags {
        lmdb::core::DbFlags::empty()
    }

    pub fn create(env: &lmdb::Environment) -> BlobToRecordTable<V, T> {
        BlobToRecordTable::new_from_handle(env.create_db(T::as_str(), Self::flags()).unwrap())
    }

    pub fn open(env: &lmdb::Environment) -> BlobToRecordTable<V, T> {
        BlobToRecordTable::new_from_handle(env.get_db(T::as_str(), Self::flags()).unwrap())
    }

    fn new_from_handle(db: lmdb::DbHandle) -> BlobToRecordTable<V, T> {
        BlobToRecordTable {db: db, _v: PhantomData, _t: PhantomData}
    }

    #[inline]
    pub fn bind_to_txn<'a>(&self, txn: &'a lmdb::Transaction) -> BoundBlobToRecordTable<'a, V, T> {
        BoundBlobToRecordTable {
            db: txn.bind(&self.db),
            _v: PhantomData, _t: PhantomData}
    }

    #[inline]
    pub fn bind_to_ro_txn<'a>(&self, txn: &'a lmdb::ReadonlyTransaction) -> BoundBlobToRecordTable<'a, V, T> {
        BoundBlobToRecordTable {
            db: txn.bind(&self.db),
            _v: PhantomData, _t: PhantomData}
    }
}

impl<'a, V, T> BoundBlobToRecordTable<'a, V, T>
where V: Sized + ToMdbValue + FromMdbValue,
      T: Tablename
{
    // fails if key exists.
    #[inline]
    pub fn insert(&self, key: &[u8], val: &V) -> MdbResult<()> {
        self.db.insert(&key, val)
    }

    // XXX: Should go into ReadonlyBound...
    #[inline]
    pub fn lookup(&self, key: &[u8]) -> MdbResult<V> {
        self.db.get::<V>(&key)
    }
}


// Can we insert zero-sized values? Right now we insert "S".
impl<K, T> KeyOnlyTable<K, T>
where K: Sized + ToMdbValue,
      T: Tablename
{
    fn flags() -> lmdb::core::DbFlags {
        lmdb::core::DbFlags::empty()
    }

    pub fn create(env: &lmdb::Environment) -> KeyOnlyTable<K, T> {
        KeyOnlyTable::new_from_handle(env.create_db(T::as_str(), Self::flags()).unwrap())
    }

    pub fn open(env: &lmdb::Environment) -> KeyOnlyTable<K, T> {
        KeyOnlyTable::new_from_handle(env.get_db(T::as_str(), Self::flags()).unwrap())
    }

    fn new_from_handle(db: lmdb::DbHandle) -> KeyOnlyTable<K, T> {
        KeyOnlyTable {db: db, _k: PhantomData, _t: PhantomData}
    }

    #[inline]
    pub fn insert(&self, txn: &Transaction, key: &K) -> MdbResult<()> {
        let db = txn.bind(&self.db);
        db.insert(key, &"S")
    }

    #[inline]
    pub fn insert_multiple<I>(&self, txn: &Transaction, keys: I) -> MdbResult<()> where I: Iterator<Item=K> {
        let db = txn.bind(&self.db);
        for key in keys {
            try!(db.insert(&key, &"S"));
        }
        Ok(())
    }
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

    #[inline]
    pub fn bind_to_txn<'a>(&self, txn: &'a lmdb::Transaction) -> BoundIntToRecordTable<'a, K, V, T> {
        BoundIntToRecordTable {
            db: txn.bind(&self.db),
            _k: PhantomData, _v: PhantomData, _t: PhantomData}
    }

    #[inline]
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
    #[inline]
    pub fn insert(&self, key: &K, val: &V) -> MdbResult<()> {
        self.db.insert(key, val)
    }

    // XXX: Should go into ReadonlyBound...
    #[inline]
    pub fn lookup(&self, key: &K) -> MdbResult<V> {
        self.db.get::<V>(key)
    }

    #[inline]
    pub fn update<F>(&self, key: &K, mut update: F) -> MdbResult<()>
        where F: FnMut(&mut V) -> bool {

        let mut cursor = try!(self.db.new_cursor());
        try!(cursor.to_key(key));

        let mut value: V = try!(cursor.get_value());

        let needs_update = update(&mut value);

        if needs_update {
            try!(cursor.replace(&value));
        }

        Ok(())
    }

    #[inline]
    pub fn insert_or_update<N, F>(&self, key: &K, insert_fn: N, mut update_fn: F) -> MdbResult<()>
        where
                N: Fn() -> V,
                F: FnMut(&mut V) -> bool {

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

    /// Returns the old value, or None.
    #[inline]
    pub fn update_or_insert_value<F>(&self, key: &K, update_fn:F, insert_value: V) -> MdbResult<Option<V>>
        where
                F: Fn(&V) -> V {

        // Trying to update first
        {
                let mut cursor = try!(self.db.new_cursor());
                if let Ok(_) = cursor.to_key(key) {
                        let orig_value: V = try!(cursor.get_value());
                        let new_value = update_fn(&orig_value);
                        try!(cursor.replace(&new_value));
                        return Ok(Some(orig_value));
                }
        }

        // Now try to insert
        {
            try!(self.db.insert(key, &insert_value));
            return Ok(None);
        }
    }

    #[inline]
    pub fn insert_or_update_default<F>(&self, key: &K, mut update_fn: F) -> MdbResult<bool>
        where
                V: Default,
                F: FnMut(&mut V) -> bool {

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

impl<K, V, T> KeyToRecordTable<K, V, T>
where K: Sized + ToMdbValue,
      V: Sized + ToMdbValue + FromMdbValue,
      T: Tablename
{
    fn flags() -> lmdb::core::DbFlags {
        lmdb::core::DbFlags::empty()
    }

    pub fn create(env: &lmdb::Environment) -> KeyToRecordTable<K, V, T> {
        KeyToRecordTable::new_from_handle(env.create_db(T::as_str(), Self::flags()).unwrap())
    }

    pub fn open(env: &lmdb::Environment) -> KeyToRecordTable<K, V, T> {
        KeyToRecordTable::new_from_handle(env.get_db(T::as_str(), Self::flags()).unwrap())
    }

    fn new_from_handle(db: lmdb::DbHandle) -> KeyToRecordTable<K, V, T> {
        KeyToRecordTable {db: db, _k: PhantomData, _v: PhantomData, _t: PhantomData}
    }

    #[inline]
    pub fn insert(&self, txn: &Transaction, key: &K, val: &V) -> MdbResult<()> {
        let db = txn.bind(&self.db);
        db.insert(key, val)
    }

    #[inline]
    pub fn insert_or_update_default<F>(&self, txn: &Transaction, key: &K, mut update_fn: F) -> MdbResult<bool>
        where
                V: Default,
                F: FnMut(&mut V) -> bool {

        let db = txn.bind(&self.db);

        // Trying to update first
        {
                let mut cursor = try!(db.new_cursor());
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
                try!(db.insert(key, &value));
            }
            return Ok(needs_update);
        }
    }

    #[inline]
    pub fn bind_to_ro_txn<'a>(&self, txn: &'a lmdb::ReadonlyTransaction) -> BoundKeyToRecordTable<'a, K, V, T> {
        BoundKeyToRecordTable {
            db: txn.bind(&self.db),
            _k: PhantomData, _v: PhantomData, _t: PhantomData}
    }
}

impl<'a, K, V, T> BoundKeyToRecordTable<'a, K, V, T>
where K: Sized + ToMdbValue,
      V: Sized + ToMdbValue + FromMdbValue,
      T: Tablename
{
    // fails if key exists.
    #[inline]
    pub fn insert(&self, key: &K, val: &V) -> MdbResult<()> {
        self.db.insert(key, val)
    }

    // XXX: Should go into ReadonlyBound...
    #[inline]
    pub fn lookup(&self, key: &K) -> MdbResult<V> {
        self.db.get::<V>(key)
    }

/*
    pub fn update<F>(&self, key: &K, mut update: F) -> MdbResult<()>
        where F: FnMut(&mut V) -> bool {

        let mut cursor = try!(self.db.new_cursor());
        try!(cursor.to_key(key));

        let mut value: V = try!(cursor.get_value());

        let needs_update = update(&mut value);

        if needs_update {
            try!(cursor.replace(&value));
        }

        Ok(())
    }

    pub fn insert_or_update<N, F>(&self, key: &K, insert_fn: N, mut update_fn: F) -> MdbResult<()>
        where
                N: Fn() -> V,
                F: FnMut(&mut V) -> bool {

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

    pub fn insert_or_update_default<F>(&self, key: &K, mut update_fn: F) -> MdbResult<bool>
        where
                V: Default,
                F: FnMut(&mut V) -> bool {

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
*/
}
