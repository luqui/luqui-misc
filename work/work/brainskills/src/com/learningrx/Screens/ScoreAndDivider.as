package com.learningrx.Screens
{
	import flash.display.Sprite;
	import flash.text.TextField;
	import flash.text.TextFormat;
	import flash.text.TextFormatAlign;
	import flash.text.TextFieldAutoSize;
	import flash.text.AntiAliasType;
	import flash.filters.BevelFilter;
	import flash.filters.BitmapFilterQuality;
	import flash.filters.BitmapFilterType;	
	
	import com.learningrx.*;
	
	public class ScoreAndDivider extends Sprite
	{
		private var _Parent:Framework;
		private var _ProgressBackground:Sprite;
		private var _ProgressBar:Sprite;
		private var _DividingLines:Sprite;
		private var _WrongScoreBox:Sprite = new Sprite;
		private var _WrongScoreTextField:TextField = new TextField;
		private var _RightScoreBox:Sprite = new Sprite;
		private var _RightScoreTextField:TextField = new TextField;
		private var _ProgressBackgroundHeight:Number = 15;
		private var _ScoreBoxWidth:Number = 60;
		private var _ScoreBoxHeight:Number = 40;
		private var _ScoreBoxCornerRadius:Number = 6;
		private var _ScoreLabelFont:String = 'Arial Rounded MT Bold';
		private var _ScoreLabelFontSize:Number = 12;
		private var _ScoreLabelColor:Number = 0x0066FF;
		private var _ScoreFont:String = 'Arial Rounded MT Bold';
		private var _ScoreFontSize:Number = 28;
		private var _RightAnswerColor:Number = 0x00FF00;
		private var _WrongAnswerColor:Number = 0xFF0000;
		
		public function ScoreAndDivider(pParent:Framework)
		{
			_Parent = pParent;
			DrawScoreBox(_RightScoreBox, _RightScoreTextField, 'Right', _RightAnswerColor);
			DrawScoreBox(_WrongScoreBox, _WrongScoreTextField, 'Wrong', _WrongAnswerColor);
			DrawProgressBackground();
			DrawProgressBar();
			DrawDividingLines();
			_RightScoreBox.x = this.width * .5 - 50 - _RightScoreBox.width;
			_WrongScoreBox.x = this.width * .5 + 50;
			_RightScoreBox.y = _WrongScoreBox.y = _ProgressBackground.y + _ProgressBackground.height +5;
		}
		
		public function UpdateProgressBar(pPercentage:Number):void
		{
			_ProgressBar.width = _ProgressBackground.width * pPercentage / 100;
		}

		public function UpdateScoreDisplay(pRightAnswers:Number, 
		                                   pWrongAnswers:Number):void
		{
			_RightScoreTextField.text = pRightAnswers.toString();
			_RightScoreTextField.x = (_ScoreBoxWidth - _RightScoreTextField.width) / 2;
			_WrongScoreTextField.text = pWrongAnswers.toString();
			_WrongScoreTextField.x = (_ScoreBoxWidth - _WrongScoreTextField.width) / 2;
		}

		private function DrawDividingLines():void
		{
			_DividingLines = new Sprite;
			var dividingLine1 = new DividingLine(_ProgressBackground.width);
			Utilities.AddChildToDisplayList(_DividingLines, dividingLine1);
			var dividingLine2 = new DividingLine(_ProgressBackground.width);
			Utilities.AddChildToDisplayList(_DividingLines, dividingLine2);
			dividingLine2.y = _ProgressBackgroundHeight;
			Utilities.AddChildToDisplayList(this, _DividingLines);
		}
		
		private function DrawScoreBox(pScoreBox:Sprite,
												pScoreTextField:TextField,
												pLabelText:String,
												pScoreColor:Number):Sprite
		{
			var label = new TextField;
			label.antiAliasType = AntiAliasType.ADVANCED;
			label.embedFonts = true;
			label.autoSize = TextFieldAutoSize.CENTER;
			label.selectable = false;
			label.width = _ScoreBoxWidth;
			var format:TextFormat = new TextFormat();
			format.font = _ScoreLabelFont;
			format.size = _ScoreLabelFontSize;
			format.color = _ScoreLabelColor;
			format.align = TextFormatAlign.CENTER;
			label.defaultTextFormat = format;
			label.text = pLabelText;
			
			pScoreTextField.antiAliasType = AntiAliasType.ADVANCED;
			pScoreTextField.embedFonts = true;
			pScoreTextField.autoSize = TextFieldAutoSize.CENTER;
			pScoreTextField.selectable = false;
			pScoreTextField.width = _ScoreBoxWidth;
			format = new TextFormat();
			format.font = _ScoreFont;
			format.size = _ScoreFontSize;
			format.color = pScoreColor;
			format.align = TextFormatAlign.CENTER;
			pScoreTextField.defaultTextFormat = format;
			pScoreTextField.text = '0';
			
			var outline = new Sprite;
			outline.graphics.lineStyle(1, 0x339900, 1, true, "none", "none", "round");
			outline.graphics.drawRoundRect(0, 0, _ScoreBoxWidth, _ScoreBoxHeight, _ScoreBoxCornerRadius, _ScoreBoxCornerRadius);
			AddBevelFilter(outline);
			Utilities.AddChildToDisplayList(pScoreBox, label);
			Utilities.AddChildToDisplayList(pScoreBox, outline);
			Utilities.AddChildToDisplayList(pScoreBox, pScoreTextField);
			outline.y = label.y + label.height + 2;
			pScoreTextField.y = outline.y + (_ScoreBoxHeight - pScoreTextField.textHeight) / 2;
			outline.x = 0;
			label.x = (_ScoreBoxWidth - label.width) / 2;
			pScoreTextField.x = (_ScoreBoxWidth - pScoreTextField.width) / 2;
			Utilities.AddChildToDisplayList(this, pScoreBox);
		}

		private function DrawProgressBar():void
		{
			_ProgressBar = new Sprite();
			_ProgressBar.graphics.beginFill(0x339900, 1); 
			_ProgressBar.graphics.lineStyle(0, 0x339900, 0, true, "none", "none", "round");
			_ProgressBar.graphics.drawRect(0, 0, 1, _ProgressBackgroundHeight);
			_ProgressBar.graphics.endFill();
			_ProgressBar.x = _ProgressBackground.x;
			Utilities.AddChildToDisplayList(this, _ProgressBar);
		}

		private function DrawProgressBackground():void
		{
			_ProgressBackground = new Sprite();
			_ProgressBackground.graphics.beginFill(0x003366, 1); 
			_ProgressBackground.graphics.lineStyle(0, 0x003366, 0, true, "none", "none", "round");
			_ProgressBackground.graphics.drawRect(0, 0, _Parent.GAME_WIDTH - 4, _ProgressBackgroundHeight);
			_ProgressBackground.graphics.endFill(); 
			Utilities.AddChildToDisplayList(this, _ProgressBackground);
		}

		private function AddBevelFilter(pSprite:Sprite):void
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
			pSprite.filters = [bevel];
		}
	}
}