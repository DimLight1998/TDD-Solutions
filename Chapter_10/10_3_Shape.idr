module Chapter_10.10_3_Shape

export
data Shape
  = Triangle Double Double
  | Rectangle Double Double
  | Circle Double

export
triangle : Double -> Double -> Shape
triangle = Triangle

export
rectangle : Double -> Double -> Shape
rectangle = Rectangle

export
circle : Double -> Shape
circle = Circle

-- 10.3 exercise 2
public export
data ShapeView : Shape -> Type where
  STriangle : ShapeView (triangle base height)
  SRectangle : ShapeView (rectangle width height)
  SCircle : ShapeView (circle radius)

export
total
shapeView : (shape : Shape) -> ShapeView shape
shapeView (Triangle b h) = STriangle {base = b} {height = h}
shapeView (Rectangle w h) = SRectangle {width = w} {height = h}
shapeView (Circle radius) = SCircle {radius = radius}
