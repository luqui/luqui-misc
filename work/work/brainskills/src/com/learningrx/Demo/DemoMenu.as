package com.learningrx.Demo
{
	import flash.display.Sprite;
	import flash.display.SimpleButton; 
	import flash.events.*;
	import flash.net.*;
	import flash.text.TextField;
	import flash.text.TextFormat;
	import flash.text.TextFormatAlign;
	import flash.text.TextFieldAutoSize;
	import flash.text.AntiAliasType;
	import flash.filters.BevelFilter;
	import flash.filters.DropShadowFilter;
	import flash.filters.BitmapFilterQuality;
	import flash.filters.BitmapFilterType;	
	
	import com.learningrx.*
	
	public class DemoMenu extends Sprite
	{
		private var _Width:Number;
		private var _Height:Number;
		private var _Leading:Number = 16;

		private var _Parent:Framework;
		private var _DropShadow:DropShadowFilter = new DropShadowFilter();
		private var _SelectAnExercise:SelectAnExercise;
		private var _AAHeader:AAHeader;
		private var _AABasicButton:BasicLevelButton;
		private var _AAIntermediateButton:IntermediateButton;
		private var _AAAdvancedButton:AdvancedButton;
		private var _CFHeader:CFHeader;
		private var _CFIntermediateButton:IntermediateButton;
		private var _CFBasicButton:BasicLevelButton;
		private var _CFAdvancedButton:AdvancedButton;
		private var _FNHeader:FNHeader;
		private var _FNBasicButton:BasicLevelButton;
		private var _FNAdvancedButton:AdvancedButton;
		private var _InstructionsText:InstructionsText;
		private var _Levels:Object;
		private var _IntroText:TextField;
		private var _HeaderText:TextField;
		
		public function DemoMenu(pParent:Framework)
		{
			_Parent = pParent;
			_Width = _Parent.GAME_WIDTH * .6;
			_Height = _Parent.GAME_HEIGHT * .7;
			DrawBorder();
			InitializeDropShadow();
			CreateBevelLine(30);
			CreateBevelLine(_Height - 30);
			_InstructionsText = new InstructionsText();
			InitLevels();
			_SelectAnExercise = new SelectAnExercise();
			_SelectAnExercise.x = (_Width - _SelectAnExercise.width) / 2;
			_SelectAnExercise.y = 40;
			
			_AAHeader = new AAHeader();
			_AAHeader.x = (_Width - _AAHeader.width) / 2;
			_AAHeader.y = _SelectAnExercise.y + _SelectAnExercise.height + _Leading * 2;
			_AABasicButton = new BasicLevelButton();
			_AABasicButton.scaleX = _AABasicButton.scaleY = .7;
			_AABasicButton.x = (_Width - _AABasicButton.width) / 2;
			_AABasicButton.y = _AAHeader.y + _AAHeader.height + _Leading;
			_AAIntermediateButton = new IntermediateButton();
			_AAIntermediateButton.scaleX = _AAIntermediateButton.scaleY = .7;
			_AAIntermediateButton.x = (_Width - _AAIntermediateButton.width) / 2;
			_AAIntermediateButton.y = _AABasicButton.y + _AABasicButton.height + _Leading;
			_AAAdvancedButton = new AdvancedButton();
			_AAAdvancedButton.scaleX = _AAAdvancedButton.scaleY = .7;
			_AAAdvancedButton.x = (_Width - _AAAdvancedButton.width) / 2;
			_AAAdvancedButton.y = _AAIntermediateButton.y + _AAIntermediateButton.height + _Leading;
			_AABasicButton.addEventListener(MouseEvent.CLICK, OnAABasicButtonClicked);
			_AAIntermediateButton.addEventListener(MouseEvent.CLICK, OnAAIntermediateButtonClicked);
			_AAAdvancedButton.addEventListener(MouseEvent.CLICK, OnAAAdvancedButtonClicked);
			
			_CFHeader = new CFHeader();
			_CFHeader.x = (_Width - _CFHeader.width) / 2;
			_CFHeader.y = _AAAdvancedButton.y + _AAAdvancedButton.height + _Leading * 1.5;
			_CFBasicButton = new BasicLevelButton();
			_CFBasicButton.scaleX = _CFBasicButton.scaleY = .7;
			_CFBasicButton.x = (_Width - _CFBasicButton.width) / 2;
			_CFBasicButton.y = _CFHeader.y + _CFHeader.height + _Leading;
			_CFAdvancedButton = new AdvancedButton();
			_CFAdvancedButton.scaleX = _CFAdvancedButton.scaleY = .7;
			_CFAdvancedButton.x = (_Width - _CFAdvancedButton.width) / 2;
			_CFAdvancedButton.y = _CFBasicButton.y + _CFBasicButton.height + _Leading;
			_CFBasicButton.addEventListener(MouseEvent.CLICK, OnCFBasicButtonClicked);
			_CFAdvancedButton.addEventListener(MouseEvent.CLICK, OnCFAdvancedButtonClicked);
			
			_FNHeader = new FNHeader();
			_FNHeader.x = (_Width - _FNHeader.width) / 2;
			_FNHeader.y = _CFAdvancedButton.y + _CFAdvancedButton.height + _Leading * 1.5;
			_FNBasicButton = new BasicLevelButton();
			_FNBasicButton.scaleX = _FNBasicButton.scaleY = .7;
			_FNBasicButton.x = (_Width - _FNBasicButton.width) / 2;
			_FNBasicButton.y = _FNHeader.y + _FNHeader.height + _Leading;
			_FNIntermediateButton = new IntermediateButton();
			_FNIntermediateButton.scaleX = _FNIntermediateButton.scaleY = .7;
			_FNIntermediateButton.x = (_Width - _FNIntermediateButton.width) / 2;
			_FNIntermediateButton.y = _FNBasicButton.y + _FNBasicButton.height + _Leading;
			_FNAdvancedButton = new AdvancedButton();
			_FNAdvancedButton.scaleX = _FNAdvancedButton.scaleY = .7;
			_FNAdvancedButton.x = (_Width - _FNAdvancedButton.width) / 2;
			_FNAdvancedButton.y = _FNIntermediateButton.y + _FNIntermediateButton.height + _Leading;
			_FNBasicButton.addEventListener(MouseEvent.CLICK, OnFNBasicButtonClicked);
			_FNIntermediateButton.addEventListener(MouseEvent.CLICK, OnFNIntermediateButtonClicked);
			_FNAdvancedButton.addEventListener(MouseEvent.CLICK, OnFNAdvancedButtonClicked);
			Show(_SelectAnExercise, _AAHeader, _AABasicButton, _AAIntermediateButton, _AAAdvancedButton);
			Show(_CFHeader, _CFBasicButton, _CFAdvancedButton);
			Show(_FNHeader, _FNBasicButton, _FNIntermediateButton, _FNAdvancedButton);
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
		
		private function OnAABasicButtonClicked(pEvent:MouseEvent):void
		{
			Clicked(ShowAABasic);			
		}

		private function OnAAIntermediateButtonClicked(pEvent:MouseEvent):void
		{
			Clicked(ShowAAIntermediate);			
		}

		private function OnAAAdvancedButtonClicked(pEvent:MouseEvent):void
		{
			Clicked(ShowAAAdvanced);			
		}

		private function OnCFBasicButtonClicked(pEvent:MouseEvent):void
		{
			Clicked(ShowCFBasic);
		}

		private function OnCFAdvancedButtonClicked(pEvent:MouseEvent):void
		{
			Clicked(ShowCFAdvanced);
		}

		private function OnFNBasicButtonClicked(pEvent:MouseEvent):void
		{
			Clicked(ShowFNBasic);			
		}

		private function OnFNIntermediateButtonClicked(pEvent:MouseEvent):void
		{
			Clicked(ShowFNIntermediate);
		}

		private function OnFNAdvancedButtonClicked(pEvent:MouseEvent):void
		{
			Clicked(ShowFNAdvanced);			
		}

		public function ShowAABasic():void
		{
			_Parent.ShowGame(_Levels.AABasic);
		}
		
		public function ShowAAIntermediate():void
		{
			_Parent.ShowGame(_Levels.AAIntermediate);
		}
		
		public function ShowAAAdvanced():void
		{
			_Parent.ShowGame(_Levels.AAAdvanced);
		}
		
		public function ShowCFBasic():void
		{
			_Parent.ShowGame(_Levels.CFBasic);
		}
		
		public function ShowCFAdvanced():void
		{
			_Parent.ShowGame(_Levels.CFAdvanced);
		}
		
		public function ShowFNBasic():void
		{
			_Parent.ShowGame(_Levels.FNBasic);
		}
		
		public function ShowFNIntermediate():void
		{
			_Parent.ShowGame(_Levels.FNIntermediate);
		}
		
		public function ShowFNAdvanced():void
		{
			_Parent.ShowGame(_Levels.FNAdvanced);
		}
		
		public function InitLevels():void
		{
			_Levels = 
			{
				AABasic:
				{
					Game: _Parent.AttentionArrows, 
					Level: 2, 
					Sublevel: 1, 
					Speed: 1,
					Instructions: _InstructionsText.AA_BASIC_INSTRUCTIONS
				},
				AAIntermediate:
				{
					Game: _Parent.AttentionArrows, 
					Level: 2, 
					Sublevel: 4, 
					Speed: 1, 
					Instructions: _InstructionsText.AA_INTERMEDIATE_INSTRUCTIONS
				},
				AAAdvanced:
				{
					Game: _Parent.AttentionArrows, 
					Level: 3, 
					Sublevel: 2, 
					Speed: 2, 
					Instructions: _InstructionsText.AA_ADVANCED_INSTRUCTIONS
				},
				CFBasic:
				{
					Game: _Parent.ComprehensionFigures, 
					Level: 6, 
					Sublevel: 1, 
					Speed: 1,
					Instructions: _InstructionsText.CF_BASIC_INSTRUCTIONS
				},
				CFAdvanced:
				{
					Game: _Parent.ComprehensionFigures, 
					Level: 12, 
					Sublevel: 1, 
					Speed: 2, 
					Instructions: _InstructionsText.CF_ADVANCED_INSTRUCTIONS
				},
				FNBasic:
				{
					Game: _Parent.FixationNumbers, 
					Level: 4, 
					Sublevel: 1, 
					Speed: 1,
					Instructions: _InstructionsText.FN_BASIC_INSTRUCTIONS
				},
				FNIntermediate:
				{
					Game: _Parent.FixationNumbers, 
					Level: 5, 
					Sublevel: 2, 
					Speed: 2,
					Instructions: _InstructionsText.FN_INTERMEDIATE_INSTRUCTIONS
				},
				FNAdvanced:
				{
					Game: _Parent.FixationNumbers, 
					Level: 9, 
					Sublevel: 3, 
					Speed: 1, 
					Instructions: _InstructionsText.FN_ADVANCED_INSTRUCTIONS
				}
			};
		}
			
		private function Clicked(pFunction:Function):void
		{
			_Parent.PlayClick();
			pFunction();
		}
		
		private function Show(...args):void
		{
			for (var i:Number = 0; i < args.length; ++i)
			{
				Utilities.AddChildToDisplayList(this, args[i]);
			}
		}

		private function Hide(...args):void
		{
			for (var i:Number = 0; i < args.length; ++i)
			{
				Utilities.RemoveChildFromDisplayList(this, args[i]);
			}
		}
	}
}