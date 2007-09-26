package com.learningrx.Screens
{
	import flash.text.TextField;
	import flash.text.TextFormat;
	import flash.text.TextFormatAlign;
	import flash.text.TextFieldAutoSize;
	import flash.text.AntiAliasType;
	import flash.display.Sprite;
	import flash.filters.BevelFilter;
	import flash.filters.DropShadowFilter;
	import flash.filters.BitmapFilterQuality;
	import flash.filters.BitmapFilterType;	

	import com.learningrx.*;

	public class Instructions extends Sprite
	{
		private var _DropShadow:DropShadowFilter = new DropShadowFilter();
		private var _Head:TextField = new TextField();
		private var _Subhead:TextField = new TextField();
		private var _Body:TextField = new TextField();
		private var _Width:Number = 700;
		private var _Height:Number = 550;

		public function Instructions()
		{
			DrawBorder();
			InitializeDropShadow();
			CreateBevelLine(50);
			CreateBevelLine(_Height - 50);
			CreateTextFields();
		}
		
		public function SetText(pInstructions:Object):void
		{
			_Head.text = pInstructions.Head;
			_Subhead.text = pInstructions.Subhead;
			_Body.htmlText = pInstructions.Body;
			//trace(_Body.htmlText);
		}
		
		private function CreateTextFields():void
		{
			CreateTextField(_Head, 'Arial Rounded MT Bold', 36, 0xFFFFFF, 100, 80);
			CreateTextField(_Subhead, 'Arial Rounded MT Bold', 24, 0x0066FF, 100, 130);
			CreateTextField(_Body, 'Arial', 20, 0xFFFFFF, 100, 200);
		}

		private function CreateTextField(pTextField:TextField,
													pFont:String,
													pSize:Number,
													pColor:Number,
													pX:Number,
													pY:Number):void
		{
			pTextField.antiAliasType = AntiAliasType.ADVANCED;
			pTextField.embedFonts = true;
			pTextField.autoSize = TextFieldAutoSize.CENTER;
			pTextField.wordWrap = true;
			pTextField.selectable = false;
			pTextField.width = _Width - 200;
			pTextField.x = pX;
			pTextField.y = pY;
			var format:TextFormat = new TextFormat();
			format.font = pFont;
			format.color = pColor;
			format.size = pSize;
			format.align = TextFormatAlign.CENTER;
			format.leading = 10;
			pTextField.defaultTextFormat = format;
			pTextField.text = '';
			Utilities.AddChildToDisplayList(this, pTextField);
		}
		
		private function DrawBorder():void
		{
			this.graphics.clear();
			this.graphics.beginFill(0x003366, 1); 
			this.graphics.lineStyle(2, 0x00CCFF, 0, true, "none", "none", "round");
			this.graphics.drawRoundRect(0, 0, _Width, _Height, 30, 30);
			this.graphics.endFill(); 
		}
		
		private function InitializeDropShadow():void
		{
			_DropShadow.distance = 5;
			_DropShadow.angle = 39;
			_DropShadow.alpha = 80;
			_DropShadow.blurX = 30;
			_DropShadow.blurY = 30;
			_DropShadow.quality = 3;
			this.filters = [_DropShadow];
		}

		private function CreateBevelLine(pY:Number):Object
		{
			var bevelLine:Sprite = new Sprite;
			bevelLine.graphics.lineStyle(1, 0x707070, 100, true, "none", "none", "round");
			bevelLine.graphics.moveTo(1, 0);
			bevelLine.graphics.lineTo(_Width - 1, 0);
			bevelLine.x = 0;
			bevelLine.y = pY;
			var bevelLineFilter:BevelFilter = new BevelFilter();
			bevelLineFilter.distance = 1;
			bevelLineFilter.angle = 295;
			bevelLineFilter.highlightColor = 0xFFFFFF;
			bevelLineFilter.highlightAlpha = 1;
			bevelLineFilter.shadowColor = 0x000033;
			bevelLineFilter.shadowAlpha = 1;
			bevelLineFilter.blurX = 2;
			bevelLineFilter.blurY = 2;
			bevelLineFilter.strength = 1;
			bevelLineFilter.quality = BitmapFilterQuality.HIGH;
			bevelLineFilter.type = BitmapFilterType.OUTER;
			bevelLineFilter.knockout = false;
			bevelLine.filters = [bevelLineFilter];
			Utilities.AddChildToDisplayList(this, bevelLine);
		}
   }
}