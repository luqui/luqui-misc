package com.learningrx.Screens
{
	import flash.display.Sprite;
	import flash.filters.BevelFilter;
	import flash.filters.BitmapFilterQuality;
	import flash.filters.BitmapFilterType;	
	
	import com.learningrx.*;
	
	public class DividingLine extends Sprite
	{
		
		public function DividingLine(pWidth:Number)
		{
			DrawLine(pWidth);
		}
		
		private function DrawLine(pWidth:Number):void
		{
			this.graphics.lineStyle(1, 0x707070, 1, true, "none", "none", "round");
			this.graphics.moveTo(0, 0);
			this.graphics.lineTo(pWidth, 0);
			var bevel:BevelFilter = new BevelFilter();
			bevel.distance = 1;
			bevel.angle = 295;
			bevel.highlightColor = 0xFFFFFF;
			bevel.highlightAlpha = 1;
			bevel.shadowColor = 0x000033;
			bevel.shadowAlpha = 1;
			bevel.blurX = 2;
			bevel.blurY = 2;
			bevel.strength = 1;
			bevel.quality = BitmapFilterQuality.HIGH;
			bevel.type = BitmapFilterType.OUTER;
			bevel.knockout = false;
			this.filters = [bevel];
		}
	}
}