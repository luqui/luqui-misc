uniform float4x4 xViewMatrix;
uniform Texture xBoundTexture;
sampler boundTextureSampler = sampler_state {
	texture = <xBoundTexture>;
};

struct VertexShaderInput
{
    float4 Pos      : POSITION0;
    float2 Tex      : TEXCOORD0;
};

struct VertexShaderOutput
{
    float4 Pos      : POSITION0;
    float2 Tex      : TEXCOORD0;
};

VertexShaderOutput VertexShaderFunction(VertexShaderInput inp)
{
    VertexShaderOutput outp;

    outp.Pos   = mul(inp.Pos, xViewMatrix);
    outp.Tex   = inp.Tex;

    return outp;
}

float4 PixelShaderFunction(VertexShaderOutput inp) : COLOR0
{
    float4 outp = tex2D(boundTextureSampler, inp.Tex);
    return outp;
}

technique BasicTexturedRender
{
    pass Pass1
    {
		AlphaBlendEnable = true;
		SrcBlend = SrcAlpha;
		DestBlend = InvSrcAlpha;
		
        VertexShader = compile vs_2_0 VertexShaderFunction();
        PixelShader  = compile ps_2_0 PixelShaderFunction();
    }
}

uniform Texture xScreenTexture;
uniform Texture xDistortionMap;
sampler screenTextureSampler = sampler_state {
	texture = <xScreenTexture>;
	magfilter = LINEAR;
};
sampler distortionMapSampler = sampler_state {
    texture = <xDistortionMap>;
    magfilter = LINEAR;
};

float4 DistortedPixelShaderFunction(VertexShaderOutput inp) : COLOR0
{
	float2 icoords = inp.Tex;
	icoords.y = 1-icoords.y;
	float2 coords = tex2D(distortionMapSampler, icoords);
	coords.y = 1-coords.y;
    return tex2D(screenTextureSampler, coords);
}

technique DistortionMapRender
{
    pass Pass1
    {
        VertexShader = compile vs_2_0 VertexShaderFunction();
        PixelShader  = compile ps_2_0 DistortedPixelShaderFunction();
    }
}


struct ColorVertexShaderInput {
	float4 Pos : POSITION0;
	float4 Color : COLOR0;
};

struct ColorPixelShaderInput {
    float4 Pos : POSITION0;
    float4 Color : COLOR0;
};

ColorPixelShaderInput ColorVertexShaderFunction(ColorVertexShaderInput inp)
{
    ColorPixelShaderInput outp;

    outp.Pos   = mul(inp.Pos, xViewMatrix);
    outp.Color = inp.Color;

    return outp;
}

float4 ColorPixelShaderFunction(ColorPixelShaderInput inp) : COLOR0
{
    return inp.Color;
}

technique BasicColorRender
{
    pass Pass1
    {
        VertexShader = compile vs_2_0 ColorVertexShaderFunction();
        PixelShader  = compile ps_2_0 ColorPixelShaderFunction();
    }
}
