module Chapter_10.10_3_DataStore

import Data.Vect

infixr 5 .+.

public export
data Schema = SString | SInt | (.+.) Schema Schema

public export
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (s1 .+. s2) = (SchemaType s1, SchemaType s2)

export
record DataStore (schema : Schema) where
  constructor MkData
  size : Nat
  items : Vect size (SchemaType schema)

export
empty : DataStore schema
empty = MkData 0 []

export
addToStore : (value : SchemaType schema) -> DataStore schema -> DataStore schema
addToStore value (MkData _ items) = MkData _ (value :: items)

public export
data StoreView : DataStore schema -> Type where
  SNil : StoreView empty
  SAdd : (rec : StoreView store) -> StoreView (addToStore value store)

storeViewAux : (items : Vect size (SchemaType schema)) -> StoreView (MkData _ items)
storeViewAux [] = SNil
storeViewAux (x :: xs) = SAdd {value = x} (storeViewAux xs)

export
storeView : (store : DataStore schema) -> StoreView store
storeView (MkData _ items) = storeViewAux items