package com.learningrx.Screens
{
	import flash.display.Sprite;
	import flash.filters.BevelFilter;
	import flash.filters.DropShadowFilter;
	import flash.filters.BitmapFilterQuality;
	import flash.filters.BitmapFilterType;	
	
	public class Border extends Sprite
	{
		
		public function Border()
		{
			DrawBorder();
			InitFilters();
		}
		
		private function DrawBorder():void
		{
			this.graphics.clear();
			this.graphics.lineStyle(2, 0x707070, 100, true, "none", "none", "round");
			this.graphics.drawRoundRect(0, 0, 890, 680, 30, 30);
			this.alpha = .7;
		}
		
		private function InitFilters():void
		{
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