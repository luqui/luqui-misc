package com.learningrx.FixationNumbers
{
	import flash.display.Sprite;
	import flash.geom.ColorTransform;
	import flash.filters.*;	
	import flash.text.*;
	import flash.events.MouseEvent;
	
	import com.learningrx.*
	import com.learningrx.Screens.*
	
	public class HintBox extends Sprite
	{
		private var _Parent:Game;
		private var _Outline:Sprite = new Sprite;
		private var _HintTextColor:Number = 0xFFFFFF;
		private var _ButtonWidth:Number = 60;
		private var _ButtonHeight:Number = 80;
		private var _Width:Number = _ButtonWidth * 3 + 24;
		private var _Height:Number = _ButtonHeight * 2.5;
		private var _CornerRadius:Number = 6;
		private var _LineColor:Number = 0x000000;
		private var _TextField:TextField;
		private var _TextFieldMargin:Number = 10;
		
		public function HintBox(pParent:Game)
		{
			_Parent = pParent;
			DrawOutline();
			CreateHintTextField();
		}
		
		public function DisplayHint(pHintText:String):void
		{
			_TextField.text = pHintText;
			_TextField.y = (_Outline.height - _TextField.textHeight) / 2;
		}

		private function DrawOutline():void
		{
			_Outline.graphics.lineStyle(1, 0x707070, 100, true, "none", "none", "round");
			_Outline.graphics.drawRoundRect(0, 0, _Width, _Height, _CornerRadius, _CornerRadius);
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
		
		private function CreateHintTextField():void
		{
			_TextField = new TextField();
			_TextField.x = _TextField.y = _TextFieldMargin;
			_TextField.width = _Width - 2 * _TextFieldMargin;
			_TextField.height = _Height - 2 * _TextFieldMargin;
			_TextField.antiAliasType = flash.text.AntiAliasType.ADVANCED;
			_TextField.embedFonts = true;
			_TextField.wordWrap = true;
			_TextField.autoSize = TextFieldAutoSize.LEFT
			var format:TextFormat = new TextFormat();
			format.font = 'Arial Rounded MT Bold';
			format.color = _HintTextColor;
			format.size = 24;
			format.align = TextFormatAlign.CENTER;
			_TextField.defaultTextFormat = format;
			_TextField.text = '';
			_TextField.selectable = false;
			Utilities.AddChildToDisplayList(this, _TextField);
		}
	}
}