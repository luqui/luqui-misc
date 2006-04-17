import qualified Graphics.HGL as HGL

main :: IO ()
main = 
	HGL.runGraphics $
	HGL.withWindow_ "Hello World Window" (300,200) $ \w -> do
		HGL.drawInWindow w $ HGL.text (100,100) "Hello World!"
		HGL.drawInWindow w $ HGL.ellipse (100,80) (200,100)
		HGL.getKey w
