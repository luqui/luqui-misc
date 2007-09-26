package com.learningrx.FixationNumbers
{
	import flash.display.Sprite;
	import flash.geom.ColorTransform;
	import flash.filters.*;	
	import flash.text.*;
	
	import com.learningrx.*;

	public class NumberSprite extends Sprite
	{
		private var _Parent:Game;
		private var _Number:Number;
		private var _Color:Number;
		private var _Height:Number;
		private var _TextField:TextField;
		
		public function NumberSprite(pParent:Game)
		{
			_Parent = pParent;
			_Height = _Parent.NumberSpriteHeight;
			CreateTextField();
			AddFilters();
		}
		
		private function CreateTextField():void
		{
			_TextField = new TextField();
			_TextField.antiAliasType = flash.text.AntiAliasType.ADVANCED;
			_TextField.embedFonts = true;
			_TextField.autoSize = TextFieldAutoSize.LEFT
			var format:TextFormat = new TextFormat();
			format.font = 'Arial Rounded MT Bold';
			format.color = 0xFFFFFF;
			format.size = _Height;
			_TextField.defaultTextFormat = format;
			_TextField.text = '6';
			_TextField.selectable = false;
			Utilities.AddChildToDisplayList(this, _TextField);
		}
		
		private function SetColor(pColor:Number):void
		{
			_Color = pColor;
			var colorInfo:ColorTransform = this.transform.colorTransform;
			colorInfo.color = pColor;
			_TextField.transform.colorTransform = colorInfo;
		}

		public function get DisplayColor():Number
		{
			return _Color;
		}

		public function set DisplayColor(pColor:Number):void
		{
			SetColor(pColor);
		}

		public function set DisplayNumber(pNumber:Number):void
		{
			_Number = pNumber;
			_TextField.text = _Number.toString();
		}

		public function get DisplayNumber():Number
		{
			return _Number;
		}

		private function AddFilters():void
		{
			this.filters = [Utilities.ObjectBevel, Utilities.ObjectDropShadow];
		}
		
		public function HideOutline():void
		{
			this.graphics.clear();
		}
		
		public function ShowOutline(pLineThickness:Number = 6):void
		{
			this.graphics.clear();
			this.graphics.lineStyle(pLineThickness, _Color, 100, true, "none", "none", "round");
			this.graphics.drawCircle(_TextField.textWidth / 2 + 3, _TextField.textHeight / 2 + 3, 
										    Math.max(_TextField.textWidth * .4, _TextField.textHeight * .4));
		}
	}
}