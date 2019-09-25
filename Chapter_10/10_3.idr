import Chapter_10.10_3_DataStore
import Chapter_10.10_3_Shape

-- 1
getValues : DataStore (SString .+. schema) -> List (SchemaType schema)
getValues store with (storeView store)
  getValues store | SNil = []
  getValues (addToStore value store) | SAdd rec = snd value :: getValues store | rec

-- 2
area : Shape -> Double
area s with (shapeView s)
  area (triangle base height) | STriangle = base * height / 2
  area (rectangle width height) | SRectangle = width * height
  area (circle radius) | SCircle = pi * radius * radius
