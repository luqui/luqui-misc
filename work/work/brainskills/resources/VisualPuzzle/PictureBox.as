package com.learningrx.VisualPuzzle
{
	import flash.display.Sprite;
	import flash.display.Bitmap;
	import flash.display.BitmapData;
	import flash.geom.ColorTransform;
	import flash.filters.*;	
	
	import com.learningrx.Shared.*;	

	public class PictureBox extends Sprite
	{
		private var _Parent:Exercise;
		private var _Outline:Sprite = new Sprite;
		private var _HintTextColor:Number = 0xFFFFFF;
		private var _CornerRadius:Number = 6;
		private var _LineColor:Number = 0x000000;
		private var _Image:Bitmap = new Bitmap();;
		
		public function PictureBox(pParent:Exercise,
											pWidth:Number,
											pHeight:Number)
		{
			_Parent = pParent;
			_Width = pWidth;
			_Height = pHeight;
			DrawOutline();
		}
		
		private function DrawOutline():void
		{
			_Outline.graphics.lineStyle(1, 0x707070, 100, true, "none", "none", "round");
			_Outline.graphics.drawRoundRect(0, 0, _Width, _Height, _CornerRadius, _CornerRadius);
			_Outline.filters = [Utilities.LineBevel];
			Utilities.Show(this, _Outline);
		}
		
		public function Show(pImage:Bitmap):void
		{
			_Image.bitmapData = pImage.bitmapData;
			_Image.filters = [Utilities.LineBevel, Utilities.ObjectDropShadow];
			_Image.width = _Width * .9;
			_Image.height = _Height * .9;
			_Image.x = _Width * .05
			_Image.y = _Height * .05
			Utilities.Show(this, _Image);
		}
	}
}