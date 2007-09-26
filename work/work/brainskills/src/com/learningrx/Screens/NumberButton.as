package com.learningrx.Screens
{
	import flash.display.Sprite;
	import flash.geom.ColorTransform;
	import flash.filters.*;	
	import flash.text.*;
	import flash.events.MouseEvent;
	
	import com.learningrx.*
	import com.learningrx.Screens.*
	
	public class NumberButton extends BasicButton
	{
		private var _Number:uint;
		private var _TextField:TextField;
		private var _TextFieldX:uint;
		private var _TextFieldY:uint;
		
		public function NumberButton(pParent:Game,
											  pNumber:uint,
											  pWidth:uint,
											  pHeight:uint)
		{
			super(pParent);
			_Width = pWidth;
			_Height = pHeight;
			this.mouseChildren = false;
			_Number = pNumber;
			_CornerRadius = 6;
			_UnhighlightedFillingColor = 0x003366;
			_HighlightedFillingColor = 0x0099AA;
			_LineColor = 0x666666;
			_LineThickness = 0;
			Init();
			CreateTextField();
			UnhighlightFilters();
		}
		
		override protected function MouseDownHandler(pEvent:MouseEvent):void 
		{
			HighlightFilters()
			_TextField.x = _TextFieldX + 2;
			_TextField.y = _TextFieldY + 2;
		}

		override protected function MouseUpHandler(pEvent:MouseEvent):void 
		{
			UnhighlightFilters();
			_TextField.x = _TextFieldX;
			_TextField.y = _TextFieldY;
		}

		override protected function MouseClickHandler(pEvent:MouseEvent):void 
		{
			DoClick();
			_Parent.OnNumberClicked(_Number);
		}
		
		override protected function MouseOutHandler(pEvent:MouseEvent):void 
		{
			MouseUpHandler(pEvent);
			Unhighlight();
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
			_TextField.text = _Number.toString();
			_TextField.selectable = false;
			_TextField.x = _TextFieldX = (this.width - _TextField.textWidth) / 2 - 3;
			_TextField.y = _TextFieldY = (this.height - _TextField.textHeight) / 2 - 1;
			var innerShadow:DropShadowFilter = new DropShadowFilter(3, 45, 0, 0.5, 6, 6, 1, 1, true, false);
			_TextField.filters = [innerShadow];
			Utilities.AddChildToDisplayList(this, _TextField);
		}
		
		private function SetColor(pColor:Number):void
		{
			var colorInfo:ColorTransform = this.transform.colorTransform;
			colorInfo.color = pColor;
			_TextField.transform.colorTransform = colorInfo;
		}

		private function UnhighlightFilters():void
		{
			var bevelFilter:BevelFilter = new BevelFilter();
			bevelFilter.distance = 6;
			bevelFilter.angle = 45;
			bevelFilter.highlightColor = 0xFFFFFF;
			bevelFilter.highlightAlpha = .25;
			bevelFilter.shadowColor = 0x000000;
			bevelFilter.shadowAlpha = .25;
			bevelFilter.blurX = 3;
			bevelFilter.blurY = 3;
			bevelFilter.strength = 1;
			bevelFilter.quality = BitmapFilterQuality.HIGH;
			bevelFilter.type = BitmapFilterType.INNER;
			bevelFilter.knockout = false;
			var dropShadow:DropShadowFilter = new DropShadowFilter();
			dropShadow.distance = 5;
			dropShadow.color = 0x000000;
			dropShadow.angle = 45;
			dropShadow.alpha = .5;
			dropShadow.blurX = 5;
			dropShadow.blurY = 5;
			dropShadow.quality = BitmapFilterQuality.HIGH;
			dropShadow.knockout = false;
			this.filters = [bevelFilter, dropShadow];
		}

		private function HighlightFilters():void
		{
			var bevelFilter:BevelFilter = new BevelFilter();
			bevelFilter.distance = 6;
			bevelFilter.angle = 45;
			bevelFilter.highlightAlpha = .25;
			bevelFilter.shadowAlpha = .25;
			bevelFilter.blurX = 5;
			bevelFilter.blurY = 5;
			bevelFilter.strength = 1;
			bevelFilter.quality = BitmapFilterQuality.HIGH;
			bevelFilter.type = BitmapFilterType.INNER;
			bevelFilter.knockout = false;
			bevelFilter.shadowColor = 0xFFFFFF;
			bevelFilter.highlightColor = 0x000000;
			var dropShadow:DropShadowFilter = new DropShadowFilter();
			dropShadow.distance = 2;
			dropShadow.color = 0x000000;
			dropShadow.angle = 45;
			dropShadow.alpha = .5;
			dropShadow.blurX = 5;
			dropShadow.blurY = 5;
			dropShadow.quality = BitmapFilterQuality.HIGH;
			dropShadow.knockout = false;
			this.filters = [bevelFilter, dropShadow];
		}
	}
}