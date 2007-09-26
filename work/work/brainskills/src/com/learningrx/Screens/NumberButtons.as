package com.learningrx.Screens
{
	import flash.display.Sprite;
	import flash.geom.ColorTransform;
	import flash.filters.*;	
	import flash.text.*;
	import flash.events.MouseEvent;
	
	import com.learningrx.*
	import com.learningrx.Screens.*
	
	public class NumberButtons extends Sprite
	{
		private var _Parent:Game;
		private var _Outline:Sprite = new Sprite;
		private var _Number:uint;
		private var _ButtonWidth:uint = 60;
		private var _ButtonHeight:uint = 80;
		private var _Width:uint = _ButtonWidth * 3 + 28;
		private var _Height:uint = _ButtonHeight * 4 - 2;
		private var _CornerRadius:uint = 6;
		private var _LineColor:uint = 0x000000;
		private var _Buttons:Array = new Array();
		
		public function NumberButtons(pParent:Game)
		{
			_Parent = pParent;
			DrawOutline();
			CreateButtons();
		}
		
		private function DrawOutline():void
		{
			_Outline.graphics.lineStyle(1, 0x707070, 100, true, "none", "none", "round");
			_Outline.graphics.drawRoundRect(0, 0, _Width, _Height, _CornerRadius, _CornerRadius);
			_Outline.graphics.moveTo(0, _Height * .25);
			_Outline.graphics.lineTo(_Width, _Height * .25);
			_Outline.graphics.moveTo(0, _Height * .5);
			_Outline.graphics.lineTo(_Width, _Height * .5);
			_Outline.graphics.moveTo(0, _Height * .75);
			_Outline.graphics.lineTo(_Width, _Height * .75);
			_Outline.graphics.moveTo(_Width * .33, 0);
			_Outline.graphics.lineTo(_Width * .33, _Height * .75);
			_Outline.graphics.moveTo(_Width * .67, 0);
			_Outline.graphics.lineTo(_Width * .67, _Height * .75);
			var bevelFilter:BevelFilter = new BevelFilter();
			bevelFilter.distance = 1;
			bevelFilter.angle = 295;
			bevelFilter.highlightColor = 0xFFFFFF;
			bevelFilter.highlightAlpha = 1;
			bevelFilter.shadowColor = 0x000033;
			bevelFilter.shadowAlpha = 1;
			bevelFilter.blurX = 2;
			bevelFilter.blurY = 2;
			bevelFilter.strength = 1;
			bevelFilter.quality = BitmapFilterQuality.HIGH;
			bevelFilter.type = BitmapFilterType.OUTER;
			bevelFilter.knockout = false;
			_Outline.filters = [bevelFilter];
			Utilities.AddChildToDisplayList(this, _Outline);
		}
		
		private function CreateButtons():void
		{
			_Buttons.push(new NumberButton(_Parent, 0, _ButtonWidth * 3, _ButtonHeight));
			_Buttons[0].width = _ButtonWidth * 3 + 19;
			_Buttons[0].height = _ButtonHeight;
			_Buttons[0].x = 4;
			_Buttons[0].y = 5 + _ButtonHeight * 3;
			Utilities.AddChildToDisplayList(this, _Buttons[0]);
			for (var i:uint = 1; i < 10; ++i)
			{
				_Buttons.push(new NumberButton(_Parent, i, _ButtonWidth, _ButtonHeight));
				_Buttons[i].width = _ButtonWidth;
				_Buttons[i].height = _ButtonHeight;
				_Buttons[i].x = 5 + ((i - 1) % 3) * (_ButtonWidth + 9);
				_Buttons[i].y = 5 + (Math.floor((9 - i) / 3)) * _ButtonHeight;
				Utilities.AddChildToDisplayList(this, _Buttons[i]);
			}
		}
	}
}